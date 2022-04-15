use std::convert::TryFrom;
use std::marker::PhantomData;
use std::ops::Deref;

use anyhow::ensure;
use filecoin_hashers::{Domain, HaloHasher, HashFunction, Hasher, PoseidonArity};
use generic_array::typenum::Unsigned;
use halo2_gadgets::utilities::{
    cond_swap::{CondSwapChip, CondSwapConfig},
    bool_check, ternary,
};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, Region},
    plonk::{self, Advice, Assigned, Column, ConstraintSystem, Expression, Selector},
    poly::Rotation,
};

use crate::{
    gadgets::halo2::{assign_value_then_insert, insert, AssignedBit, InsertChip, InsertConfig},
    merkle::{base_path_length, MerkleProofTrait, MerkleTreeTrait},
};

#[derive(Clone)]
pub struct MerkleConfig<H, U, V, W>
where
    H: HaloHasher,
    <H::Domain as Domain>::Field: FieldExt,
    U: PoseidonArity<<H::Domain as Domain>::Field>,
    V: PoseidonArity<<H::Domain as Domain>::Field>,
    W: PoseidonArity<<H::Domain as Domain>::Field>,
{
    hasher: H::Config,
    insert_base: InsertConfig,
    insert_sub: Option<InsertConfig>,
    insert_top: Option<InsertConfig>,
    _u: PhantomData<U>,
    _v: PhantomData<V>,
    _w: PhantomData<W>,
}

pub struct MerkleChip<H, U, V, W>
where
    H: HaloHasher,
    <H::Domain as Domain>::Field: FieldExt,
    U: PoseidonArity<<H::Domain as Domain>::Field>,
    V: PoseidonArity<<H::Domain as Domain>::Field>,
    W: PoseidonArity<<H::Domain as Domain>::Field>,
{
    config: MerkleConfig<H, U, V, W>,
}

impl<H, U, V, W> MerkleChip<H, U, V, W>
where
    H: HaloHasher,
    <H::Domain as Domain>::Field: FieldExt,
    U: PoseidonArity<<H::Domain as Domain>::Field>,
    V: PoseidonArity<<H::Domain as Domain>::Field>,
    W: PoseidonArity<<H::Domain as Domain>::Field>,
{
    pub fn construct(config: MerkleConfig<H, U, V, W>) -> Self {
        MerkleChip { config }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<<H::Domain as Domain>::Field>,
        hasher: H::Config,
        insert: (InsertConfig, Option<InsertConfig>, Option<InsertConfig>),
    ) -> MerkleConfig<H, U, V, W> {
        let (insert_base, insert_sub, insert_top) = insert;

        if V::to_usize() == 0 {
            assert!(insert_sub.is_none());
        }
        if W::to_usize() == 0 {
            assert!(insert_top.is_none());
        }

        MerkleConfig {
            hasher,
            insert_base,
            insert_sub,
            insert_top,
            _u: PhantomData,
            _v: PhantomData,
            _w: PhantomData,
        }
    }

    pub fn compute_root(
        &self,
        mut layouter: impl Layouter<<H::Domain as Domain>::Field>,
        challenge_bits: &[AssignedBit<<H::Domain as Domain>::Field>],
        leaf: &Option<<H::Domain as Domain>::Field>,
        path: &[Vec<Option<<H::Domain as Domain>::Field>>],
    ) -> Result<
        AssignedCell<<H::Domain as Domain>::Field, <H::Domain as Domain>::Field>,
        plonk::Error,
    > {
        let base_arity = U::to_usize();
        let sub_arity = V::to_usize();
        let top_arity = W::to_usize();

        let base_arity_bit_len = base_arity.trailing_zeros();
        let sub_arity_bit_len = sub_arity.trailing_zeros();
        let top_arity_bit_len = top_arity.trailing_zeros();

        let base_path_len = if top_arity > 0 {
            path.len() - 2
        } else if sub_arity > 0 {
            path.len() - 1
        } else {
            path.len()
        };

        let mut cur = None;
        let mut height = 0;
        let mut path_values = path.into_iter();
        let mut challenge_bits = challenge_bits.into_iter();

        let insert_base_chip = InsertChip::<<H::Domain as Domain>::Field, U>::construct(
            self.config.insert_base.clone(),
        );
        let insert_sub_chip = self.config.insert_sub.clone().map(|config| {
            InsertChip::<<H::Domain as Domain>::Field, V>::construct(config)
        });
        let insert_top_chip = self.config.insert_top.clone().map(|config| {
            InsertChip::<<H::Domain as Domain>::Field, W>::construct(config)
        });

        for _ in 0..base_path_len {
            let siblings = path_values.next().expect("no path elements remaining");

            assert_eq!(
                siblings.len(),
                base_arity - 1,
                "path element has incorrect number of siblings"
            );

            let index_bits: Vec<AssignedBit<<H::Domain as Domain>::Field>> = (0..base_arity_bit_len)
                .map(|_| challenge_bits.next().expect("no challenge bits remaining").clone())
                .collect();

            let preimage = if height == 0 {
                insert_base_chip.assign_value_then_insert(
                    layouter.namespace(|| format!("insert (height {})", height)),
                    &siblings,
                    leaf,
                    &index_bits,
                )?
            } else {
                insert_base_chip.insert(
                    layouter.namespace(|| format!("insert (height {})", height)),
                    &siblings,
                    &cur.take().unwrap(),
                    &index_bits,
                )?
            };

            let digest = H::hash_circuit_packed(
                layouter.namespace(|| format!("merkle hash (height {})", height)),
                // TODO: figure out a way to not clone the config on each hash function.
                self.config.hasher.clone(),
                &preimage,
            )?;

            cur = Some(digest);
            height += 1;
        }

        if sub_arity > 0 {
            let siblings = path_values.next().expect("no path elements remaining");

            assert_eq!(
                siblings.len(),
                sub_arity - 1,
                "path element has incorrect number of siblings"
            );

            let index_bits: Vec<AssignedBit<<H::Domain as Domain>::Field>> = (0..sub_arity_bit_len)
                .map(|_| challenge_bits.next().expect("no challenge bits remaining").clone())
                .collect();

            let preimage = insert_sub_chip.as_ref().unwrap().insert(
                layouter.namespace(|| format!("insert (height {})", height)),
                &siblings,
                &cur.take().unwrap(),
                &index_bits,
            )?;

            let digest = H::hash_circuit_packed(
                layouter.namespace(|| format!("merkle hash (height {})", height)),
                // TODO: figure out a way to not clone the config on each hash function.
                self.config.hasher.clone(),
                &preimage,
            )?;

            cur = Some(digest);
            height += 1;
        }

        if top_arity > 0 {
            let siblings = path_values.next().expect("no path elements remaining");

            assert_eq!(
                siblings.len(),
                top_arity - 1,
                "path element has incorrect number of siblings"
            );

            let index_bits: Vec<AssignedBit<<H::Domain as Domain>::Field>> = (0..top_arity_bit_len)
                .map(|_| challenge_bits.next().expect("no challenge bits remaining").clone())
                .collect();

            let preimage = insert_top_chip.as_ref().unwrap().insert(
                layouter.namespace(|| format!("insert (height {})", height)),
                &siblings,
                &cur.take().unwrap(),
                &index_bits,
            )?;

            let digest = H::hash_circuit_packed(
                layouter.namespace(|| format!("merkle hash (height {})", height)),
                // TODO: figure out a way to not clone the config on each hash function.
                self.config.hasher.clone(),
                &preimage,
            )?;

            cur = Some(digest);
            height += 1;
        }

        Ok(cur.unwrap())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use std::cmp::max;

    use ff::PrimeField;
    use filecoin_hashers::poseidon::PoseidonHasher;
    use generic_array::typenum::{U0, U2, U4, U8};
    use halo2_proofs::{
        circuit::SimpleFloorPlanner,
        dev::MockProver,
        pasta::{Fp, Fq},
        plonk::{Circuit, Fixed},
    };
    use merkletree::store::VecStore;
    use rand::{Rng, SeedableRng};
    use rand_xorshift::XorShiftRng;

    use crate::{
        gadgets::halo2::{Bit, InsertChip},
        merkle::{generate_tree, MerkleTreeWrapper},
        TEST_SEED,
    };

    #[derive(Clone)]
    struct MyConfig<H, U, V, W>
    where
        H: HaloHasher,
        <H::Domain as Domain>::Field: FieldExt,
        U: PoseidonArity<<H::Domain as Domain>::Field>,
        V: PoseidonArity<<H::Domain as Domain>::Field>,
        W: PoseidonArity<<H::Domain as Domain>::Field>,
    {
        merkle: MerkleConfig<H, U, V, W>,
        advice_eq: Vec<Column<Advice>>,
    }

    struct MyCircuit<H, U, V, W>
    where
        H: HaloHasher,
        <H::Domain as Domain>::Field: FieldExt,
        U: PoseidonArity<<H::Domain as Domain>::Field>,
        V: PoseidonArity<<H::Domain as Domain>::Field>,
        W: PoseidonArity<<H::Domain as Domain>::Field>,
    {
        challenge_bits: Vec<Option<bool>>,
        leaf: Option<<H::Domain as Domain>::Field>,
        path: Vec<Vec<Option<<H::Domain as Domain>::Field>>>,
        _u: PhantomData<U>,
        _v: PhantomData<V>,
        _w: PhantomData<W>,
    }

    impl<H, U, V, W> Circuit<<H::Domain as Domain>::Field> for MyCircuit<H, U, V, W>
    where
        H: HaloHasher,
        <H::Domain as Domain>::Field: FieldExt,
        U: PoseidonArity<<H::Domain as Domain>::Field>,
        V: PoseidonArity<<H::Domain as Domain>::Field>,
        W: PoseidonArity<<H::Domain as Domain>::Field>,
    {
        type Config = MyConfig<H, U, V, W>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            MyCircuit {
                challenge_bits: vec![],
                leaf: None,
                path: vec![],
                _u: PhantomData,
                _v: PhantomData,
                _w: PhantomData,
            }
        }

        fn configure(meta: &mut ConstraintSystem<<H::Domain as Domain>::Field>) -> Self::Config {
            // The number of required columns scales with arity, therefore the largest arity (always
            // the base arity) should be used to calculate the number of columns.
            let num_cols_hasher = H::column_spec::<U>();
            let num_cols_insert_base = H::column_spec::<U>();

            let num_advice_eq = max(num_cols_hasher.advice_eq, num_cols_insert_base.advice_eq);
            let num_advice_neq = max(num_cols_hasher.advice_neq, num_cols_insert_base.advice_neq);
            let num_fixed_eq = max(num_cols_hasher.fixed_eq, num_cols_insert_base.fixed_eq);
            let num_fixed_neq = max(num_cols_hasher.fixed_neq, num_cols_insert_base.fixed_neq);

            let advice_eq: Vec<Column<Advice>> =
                (0..num_advice_eq).map(|_| meta.advice_column()).collect();

            let advice_neq: Vec<Column<Advice>> =
                (0..num_advice_neq).map(|_| meta.advice_column()).collect();

            let fixed_eq: Vec<Column<Fixed>> =
                (0..num_fixed_eq).map(|_| meta.fixed_column()).collect();

            let fixed_neq: Vec<Column<Fixed>> =
                (0..num_fixed_neq).map(|_| meta.fixed_column()).collect();

            for col in advice_eq.iter() {
                meta.enable_equality(*col);
            }
            for col in fixed_eq.iter() {
                meta.enable_equality(*col);
            }

            let hasher = H::configure::<U>(meta, &advice_eq, &advice_neq, &fixed_eq, &fixed_neq);

            let insert_base = InsertChip::<<H::Domain as Domain>::Field, U>::configure(
                meta,
                &advice_eq,
                &advice_neq,
            );

            let insert_sub = if V::to_usize() == 0 {
                None
            } else {
                Some(InsertChip::<<H::Domain as Domain>::Field, V>::configure(
                    meta,
                    &advice_eq,
                    &advice_neq,
                ))
            };

            let insert_top = if W::to_usize() == 0 {
                None
            } else {
                Some(InsertChip::<<H::Domain as Domain>::Field, W>::configure(
                    meta,
                    &advice_eq,
                    &advice_neq,
                ))
            };

            let merkle = MerkleChip::configure(
                meta,
                hasher,
                (insert_base, insert_sub, insert_top),
            );

            MyConfig {
                merkle,
                advice_eq,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<<H::Domain as Domain>::Field>,
        ) -> Result<(), plonk::Error> {
            let chip = MerkleChip::construct(config.merkle.clone());

            // Allocate the challenge bits.
            let challenge_bits: Vec<AssignedBit<<H::Domain as Domain>::Field>> = layouter.assign_region(
                || "challenge_bits",
                |mut region| {
                    let row = 0;
                    self.challenge_bits
                        .iter()
                        .enumerate()
                        .map(|(i, opt)| {
                            region.assign_advice(
                                || format!("challenge bit {}", i),
                                config.advice_eq[i],
                                row,
                                || opt.map(Bit).ok_or(plonk::Error::Synthesis),
                            )
                        })
                        .collect()
                },
            )?;

            // Compute the root from the provided Merkle path.
            let root = chip.compute_root(layouter, &challenge_bits, &self.leaf, &self.path)?;

            if let Some(root) = root.value() {
                let expected_root =
                    expected_root::<H>(&self.challenge_bits, &self.leaf, &self.path);
                assert_eq!(root, &expected_root);
            }

            Ok(())
        }
    }

    impl<H, U, V, W> MyCircuit<H, U, V, W>
    where
        H: HaloHasher,
        <H::Domain as Domain>::Field: FieldExt,
        U: PoseidonArity<<H::Domain as Domain>::Field>,
        V: PoseidonArity<<H::Domain as Domain>::Field>,
        W: PoseidonArity<<H::Domain as Domain>::Field>,
    {
        fn with_witness(
            challenge_bits: Vec<bool>,
            leaf: <H::Domain as Domain>::Field,
            path: Vec<Vec<<H::Domain as Domain>::Field>>,
        ) -> Self {
            MyCircuit {
                challenge_bits: challenge_bits.into_iter().map(Some).collect(),
                leaf: Some(leaf),
                path: path.into_iter().map(|siblings| siblings.into_iter().map(Some).collect()).collect(),
                _u: PhantomData,
                _v: PhantomData,
                _w: PhantomData,
            }
        }
    }

    fn expected_root<H>(
        challenge_bits: &[Option<bool>],
        leaf: &Option<<H::Domain as Domain>::Field>,
        path: &[Vec<Option<<H::Domain as Domain>::Field>>],
    ) -> <H::Domain as Domain>::Field
    where
        H: HaloHasher,
        <H::Domain as Domain>::Field: FieldExt,
    {
        let mut cur = leaf.clone().unwrap();
        let mut challenge_bits = challenge_bits.iter().map(|opt| opt.unwrap());

        for siblings in path.iter() {
            let arity = siblings.len() + 1;
            let index_bit_len = arity.trailing_zeros() as usize;

            let index = (0..index_bit_len).fold(0, |acc, i| {
                let bit = challenge_bits.next().unwrap() as usize;
                acc + (bit << i)
            });

            let mut preimage = Vec::<u8>::with_capacity(arity << 5);
            for sib in &siblings[..index] {
                preimage.extend_from_slice(sib.clone().unwrap().to_repr().as_ref())
            }
            preimage.extend_from_slice(cur.to_repr().as_ref());
            for sib in &siblings[index..] {
                preimage.extend_from_slice(sib.clone().unwrap().to_repr().as_ref())
            }

            cur = H::Function::hash(&preimage).into();
        }

        cur
    }

    fn test_halo2_merkle_chip_inner<H, U, V, W>()
    where
        H: 'static + HaloHasher,
        <H::Domain as Domain>::Field: FieldExt,
        U: PoseidonArity<<H::Domain as Domain>::Field>,
        V: PoseidonArity<<H::Domain as Domain>::Field>,
        W: PoseidonArity<<H::Domain as Domain>::Field>,
    {
        const BASE_HEIGHT: u32 = 2;

        let base_arity = U::to_usize();
        let sub_arity = V::to_usize();
        let top_arity = W::to_usize();

        let mut num_leafs = base_arity.pow(BASE_HEIGHT);
        if sub_arity > 0 {
            num_leafs *= sub_arity;
        }
        if top_arity > 0 {
            num_leafs *= top_arity;
        }

        let mut rng = XorShiftRng::from_seed(TEST_SEED);
        let (_, tree) = generate_tree::<MerkleTreeWrapper<H, VecStore<H::Domain>, U, V, W>, _>(
            &mut rng,
            num_leafs,
            None,
        );

        let challenge_bit_len = num_leafs.trailing_zeros() as usize;

        for challenge in 0..num_leafs {
            let merkle_proof = tree.gen_proof(challenge).unwrap();

            let leaf = merkle_proof.leaf().into();
            let mut challenge_bits = Vec::with_capacity(challenge_bit_len);
            let path = merkle_proof
                .path()
                .into_iter()
                .map(|(siblings, index)| {
                    let arity = siblings.len() + 1;
                    let index_bit_len = arity.trailing_zeros() as usize;
                    for i in 0..index_bit_len {
                        challenge_bits.push((index >> i) & 1 == 1);
                    }
                    siblings.into_iter().map(Into::into).collect()
                })
                .collect();

            let circ = MyCircuit::<H, U, V, W>::with_witness(challenge_bits, leaf, path);
            let pub_inputs = vec![];
            // let k = MyCircuit::<H, U, V, W>::k();
            let k = 17;
            let prover = MockProver::run(k, &circ, pub_inputs).unwrap();
            dbg!(prover.verify().is_ok());
            // assert!(prover.verify().is_ok());
        }
    }

    #[test]
    fn test_halo2_merkle_chip() {
        // Arity 2
        test_halo2_merkle_chip_inner::<PoseidonHasher<Fp>, U2, U0, U0>();

        /*
        // Arity 4
        test_halo2_merkle_chip_inner::<Fp, U4, U0, U0>();

        // Arity 8
        test_halo2_merkle_chip_inner::<Fp, U8, U0, U0>();
        test_halo2_merkle_chip_inner::<Fp, U8, U8, U0>();

        // Arity 8-2
        test_halo2_merkle_chip_inner::<Fp, U8, U2, U0>();
        test_halo2_merkle_chip_inner::<Fp, U8, U8, U2>();

        // Arity 8-4
        test_halo2_merkle_chip_inner::<Fp, U8, U4, U0>();
        test_halo2_merkle_chip_inner::<Fp, U8, U8, U4>();

        // Arity 8-4-2
        test_halo2_merkle_chip_inner::<Fp, U8, U4, U2>();
        */
    }
}
