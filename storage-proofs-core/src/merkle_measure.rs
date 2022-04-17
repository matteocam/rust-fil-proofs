use filecoin_hashers::{poseidon::PoseidonHasher, Hasher}; 
use merkletree::store::VecStore; 

use generic_array::typenum::{Unsigned, U0, U2, U4, U8};  
use storage_proofs_core::merkle::MerkleProof;

use bellperson::{
    groth16::{generate_random_parameters, create_random_proof, prepare_verifying_key, verify_proof},
    Circuit, ConstraintSystem, SynthesisError,
};
use blstrs::{Bls12, Scalar as Fr};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use storage_proofs_core::{
    gadgets::por::PoRCircuit,
    merkle::{generate_tree, MerkleTreeTrait, MerkleTreeWrapper, ResTree},
    TEST_SEED,
};

type H = PoseidonHasher;
type Tree = MerkleTreeWrapper<PoseidonHasher, VecStore<<H as Hasher>::Domain>, U2, U0, U0>;

struct MyCircuit {
    tree: Tree,
    challenges: Vec<usize>,
}

impl Circuit<Fr> for MyCircuit {
    // Verify each challenge's Merkle proof in the circuit.
    fn synthesize<CS: ConstraintSystem<Fr>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        for c in self.challenges.clone() {
            let merkle_proof:MerkleProof<<Tree as MerkleTreeTrait>::Hasher, <Tree as MerkleTreeTrait>::Arity, <Tree as MerkleTreeTrait>::SubTreeArity, <Tree as MerkleTreeTrait>::TopTreeArity>
                 = self.tree.gen_proof(c).expect("failed to generate Merkle proof");
            let circ = PoRCircuit::<ResTree<Tree>>::new(merkle_proof, false);
            circ.synthesize(&mut cs.namespace(|| format!("challenge {} merkle proof", c)))
                .expect("failed to synthesize circuit");
        }
        Ok(())
    }
}

impl MyCircuit {
    fn public_inputs(&self) -> Vec<Fr> {
        let mut pub_inputs = vec![];
        for c in self.challenges.clone() {
            pub_inputs.push(Fr::from(c as u64));
            pub_inputs.push(self.tree.root().into());
        }
        pub_inputs
    }
}

fn main() {
    // Set your tree type; you can change the hasher and arity.
    type Tree = MerkleTreeWrapper<PoseidonHasher, VecStore<<PoseidonHasher as Hasher>::Domain>, U2, U0, U0>;

    // Set your tree size.
    let num_leafs = 8; // TODO: set to appropriate number 2**27 at most

    // Set your Merkle challenges; each element of the vector is the index of a leaf,
    // i.e. an integer in `0..num_laefs`, whose Merkle proof the circuit verifies.
    let challenges = vec![];

    // Create the Groth16 CRS for this circuit.
    let params = {
        let mut rng = XorShiftRng::from_seed(TEST_SEED);
        let (_leafs, tree) = generate_tree::<Tree, _>(&mut rng, num_leafs, None);
        let circ = MyCircuit {
            tree,
            challenges: challenges.clone(),
        };
        let mut rng = XorShiftRng::from_seed(TEST_SEED);
        generate_random_parameters(circ, &mut rng).unwrap()
    };
    // "Prepare" your verifying key.
    let pvk = prepare_verifying_key::<Bls12>(&params.vk);

    // Instantiate a circuit using the same tree that was used above.
    let mut rng = XorShiftRng::from_seed(TEST_SEED);
    let (_leafs, tree) = generate_tree::<Tree, _>(&mut rng, num_leafs, None);
    let circ = MyCircuit {
        tree,
        challenges,
    };
    let pub_inputs = circ.public_inputs();

    // Create a Groth16 proof.
    let mut rng = XorShiftRng::from_seed(TEST_SEED);
    let proof = create_random_proof(circ, &params, &mut rng).unwrap();

    // Verify proof.
    assert!(verify_proof(&pvk, &proof, &pub_inputs).unwrap());
}