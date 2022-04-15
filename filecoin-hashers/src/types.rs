use std::fmt::Debug;
use std::hash::Hash as StdHash;

#[cfg(feature = "poseidon")]
pub use crate::poseidon_types::*;

use anyhow::ensure;
use bellperson::{
    gadgets::{boolean::Boolean, num::AllocatedNum},
    ConstraintSystem, SynthesisError,
};
use blstrs::Scalar as Fr;
use ec_gpu::GpuField;
use ff::{Field, PrimeField};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter},
    plonk::{self, Advice, Column, Fixed},
};
use merkletree::{
    hash::{Algorithm as LightAlgorithm, Hashable as LightHashable},
    merkle::Element,
};
use rand::RngCore;
use serde::{de::DeserializeOwned, Serialize};

pub trait Domain:
    Ord
    + Copy
    + Clone
    + AsRef<[u8]>
    + Default
    + Debug
    + Eq
    + Send
    + Sync
    + From<Self::Field>
    + Into<Self::Field>
    + From<[u8; 32]>
    + Serialize
    + DeserializeOwned
    + Element
    + StdHash
{
    type Field: PrimeField + GpuField;

    #[allow(clippy::wrong_self_convention)]
    fn into_bytes(&self) -> Vec<u8> {
        self.as_ref().to_vec()
    }

    fn try_from_bytes(bytes: &[u8]) -> anyhow::Result<Self> {
        ensure!(bytes.len() == Self::byte_len(), "invalid number of bytes");
        let mut array = [0u8; 32];
        array.copy_from_slice(bytes);
        Ok(array.into())
    }

    /// Write itself into the given slice, LittleEndian bytes.
    fn write_bytes(&self, dest: &mut [u8]) -> anyhow::Result<()> {
        let n = Self::byte_len();
        ensure!(dest.len() >= n, "invalid number of bytes");
        dest[..n].copy_from_slice(self.as_ref());
        Ok(())
    }

    fn random<R: RngCore>(rng: &mut R) -> Self {
        // Generating a field element then converting it ensures that we stay within the field.
        Self::Field::random(rng).into()
    }
}

pub trait HashFunction<T: Domain>: Clone + Debug + Send + Sync + LightAlgorithm<T> {
    fn hash(data: &[u8]) -> T;
    fn hash2(a: &T, b: &T) -> T;
    fn hash_md(input: &[T]) -> T {
        // Default to binary.
        assert!(input.len() > 1, "hash_md needs more than one element.");
        input
            .iter()
            .skip(1)
            .fold(input[0], |acc, elt| Self::hash2(&acc, elt))
    }

    fn hash_leaf(data: &dyn LightHashable<Self>) -> T {
        let mut a = Self::default();
        data.hash(&mut a);
        let item_hash = a.hash();
        a.leaf(item_hash)
    }

    fn hash_single_node(data: &dyn LightHashable<Self>) -> T {
        let mut a = Self::default();
        data.hash(&mut a);
        a.hash()
    }

    fn hash_leaf_circuit<CS: ConstraintSystem<Fr>>(
        mut cs: CS,
        left: &AllocatedNum<Fr>,
        right: &AllocatedNum<Fr>,
        height: usize,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        let left_bits = left.to_bits_le(cs.namespace(|| "left num into bits"))?;
        let right_bits = right.to_bits_le(cs.namespace(|| "right num into bits"))?;

        Self::hash_leaf_bits_circuit(cs, &left_bits, &right_bits, height)
    }

    fn hash_multi_leaf_circuit<Arity: PoseidonArity<Fr>, CS: ConstraintSystem<Fr>>(
        cs: CS,
        leaves: &[AllocatedNum<Fr>],
        height: usize,
    ) -> Result<AllocatedNum<Fr>, SynthesisError>;

    fn hash_md_circuit<CS: ConstraintSystem<Fr>>(
        _cs: &mut CS,
        _elements: &[AllocatedNum<Fr>],
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        unimplemented!();
    }

    fn hash_leaf_bits_circuit<CS: ConstraintSystem<Fr>>(
        _cs: CS,
        _left: &[Boolean],
        _right: &[Boolean],
        _height: usize,
    ) -> Result<AllocatedNum<Fr>, SynthesisError> {
        unimplemented!();
    }

    fn hash_circuit<CS: ConstraintSystem<Fr>>(
        cs: CS,
        bits: &[Boolean],
    ) -> Result<AllocatedNum<Fr>, SynthesisError>;

    fn hash2_circuit<CS>(
        cs: CS,
        a: &AllocatedNum<Fr>,
        b: &AllocatedNum<Fr>,
    ) -> Result<AllocatedNum<Fr>, SynthesisError>
    where
        CS: ConstraintSystem<Fr>;
}

pub trait Hasher: Clone + Debug + Eq + Default + Send + Sync {
    type Domain: Domain + LightHashable<Self::Function> + AsRef<Self::Domain>;
    type Function: HashFunction<Self::Domain>;

    fn name() -> String;
}

pub struct ColumnSpec {
    pub advice_eq: usize,
    pub advice_neq: usize,
    pub fixed_eq: usize,
    pub fixed_neq: usize,
}

pub trait HaloHasher: Hasher
where
    <Self::Domain as Domain>::Field: FieldExt,
{
    type Config: Clone;
    type Assigned;
    type Digest;

    fn configure<A>(
        meta: &mut plonk::ConstraintSystem<<Self::Domain as Domain>::Field>,
        advice_eq: &[Column<Advice>],
        advice_neq: &[Column<Advice>],
        fixed_eq: &[Column<Fixed>],
        fixed_neq: &[Column<Fixed>],
    ) -> Self::Config
    where
        A: PoseidonArity<<Self::Domain as Domain>::Field>;

    fn column_spec<A>() -> ColumnSpec
    where
        A: PoseidonArity<<Self::Domain as Domain>::Field>;

    fn hash_circuit(
        layouter: impl Layouter<<Self::Domain as Domain>::Field>,
        config: Self::Config,
        preimage: &[Self::Assigned],
    ) -> Result<Self::Digest, plonk::Error>;

    fn hash_circuit_packed(
        layouter: impl Layouter<<Self::Domain as Domain>::Field>,
        config: Self::Config,
        preimage: &[AssignedCell<<Self::Domain as Domain>::Field, <Self::Domain as Domain>::Field>],
    ) -> Result<
        AssignedCell<<Self::Domain as Domain>::Field, <Self::Domain as Domain>::Field>,
        plonk::Error,
    >;
}
