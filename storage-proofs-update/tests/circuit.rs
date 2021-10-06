use std::marker::PhantomData;
use std::path::Path;

use bellperson::{util_cs::test_cs::TestConstraintSystem, Circuit};
use blstrs::Scalar as Fr;
use filecoin_hashers::{Domain, HashFunction, Hasher};
use generic_array::typenum::{Unsigned, U0, U2, U4, U8};
use merkletree::store::{DiskStore, StoreConfig};
use rand::SeedableRng;
use rand_xorshift::XorShiftRng;
use storage_proofs_core::{
    merkle::{MerkleProofTrait, MerkleTreeTrait, MerkleTreeWrapper},
    util::default_rows_to_discard,
    TEST_SEED,
};
use storage_proofs_update::{
    circuit,
    constants::{
        apex_leaf_count, hs, partition_count, validate_tree_r_shape, TreeD, TreeDDomain,
        TreeRDomain, TreeRHasher, SECTOR_SIZE_16_KIB, SECTOR_SIZE_1_KIB, SECTOR_SIZE_2_KIB,
        SECTOR_SIZE_32_KIB, SECTOR_SIZE_4_KIB, SECTOR_SIZE_8_KIB,
    },
    Challenges, EmptySectorUpdateCircuit, PublicParams,
};
use tempfile::tempdir;

// Selects a value for `h` via `h = hs[log2(h_select)]`; default to taking `h = hs[2]`.
const H_SELECT: u64 = 1 << 2;

fn create_tree<Tree: MerkleTreeTrait>(
    labels: &[<<Tree as MerkleTreeTrait>::Hasher as Hasher>::Domain],
    tmp_path: &Path,
    tree_name: &str,
) -> MerkleTreeWrapper<Tree::Hasher, Tree::Store, Tree::Arity, Tree::SubTreeArity, Tree::TopTreeArity>
{
    let sector_nodes = labels.len();
    let base_arity = Tree::Arity::to_usize();
    let sub_arity = Tree::SubTreeArity::to_usize();
    let top_arity = Tree::TopTreeArity::to_usize();

    // Create a single base-tree, a single sub-tree (out of base-trees), or a single top-tree
    // (out of sub-trees, each made of base-trees).
    if sub_arity == 0 && top_arity == 0 {
        let config = StoreConfig::new(
            tmp_path,
            tree_name.to_string(),
            default_rows_to_discard(sector_nodes, base_arity),
        );
        let leafs = labels.iter().copied().map(Ok);
        MerkleTreeWrapper::try_from_iter_with_config(leafs, config)
            .unwrap_or_else(|_| panic!("failed to create non-compound-tree {}", tree_name))
    } else if top_arity == 0 {
        let base_tree_count = sub_arity;
        let leafs_per_base_tree = sector_nodes / base_tree_count;
        let rows_to_discard = default_rows_to_discard(leafs_per_base_tree, base_arity);
        let base_trees: Vec<MerkleTreeWrapper<Tree::Hasher, Tree::Store, Tree::Arity>> = (0
            ..base_tree_count)
            .map(|i| {
                let config = StoreConfig::new(
                    tmp_path,
                    format!("{}-base-{}", tree_name, i),
                    rows_to_discard,
                );
                let leafs = labels[i * leafs_per_base_tree..(i + 1) * leafs_per_base_tree]
                    .iter()
                    .copied()
                    .map(Ok);
                MerkleTreeWrapper::try_from_iter_with_config(leafs, config)
                    .unwrap_or_else(|_| panic!("failed to create {} base-tree {}", tree_name, i))
            })
            .collect();
        MerkleTreeWrapper::from_trees(base_trees)
            .unwrap_or_else(|_| panic!("failed to create {} from base-trees", tree_name))
    } else {
        let base_tree_count = top_arity * sub_arity;
        let sub_tree_count = top_arity;
        let leafs_per_base_tree = sector_nodes / base_tree_count;
        let base_trees_per_sub_tree = sub_arity;
        let rows_to_discard = default_rows_to_discard(leafs_per_base_tree, base_arity);
        let sub_trees: Vec<
            MerkleTreeWrapper<Tree::Hasher, Tree::Store, Tree::Arity, Tree::SubTreeArity>,
        > = (0..sub_tree_count)
            .map(|sub_index| {
                let first_sub_leaf = sub_index * base_trees_per_sub_tree * leafs_per_base_tree;
                let base_trees: Vec<MerkleTreeWrapper<Tree::Hasher, Tree::Store, Tree::Arity>> = (0
                    ..base_trees_per_sub_tree)
                    .map(|base_index| {
                        let config = StoreConfig::new(
                            tmp_path,
                            format!("{}-sub-{}-base-{}", tree_name, sub_index, base_index),
                            rows_to_discard,
                        );
                        let first_base_leaf = first_sub_leaf + base_index * leafs_per_base_tree;
                        let leafs = labels[first_base_leaf..first_base_leaf + leafs_per_base_tree]
                            .iter()
                            .copied()
                            .map(Ok);
                        MerkleTreeWrapper::try_from_iter_with_config(leafs, config).unwrap_or_else(
                            |_| {
                                panic!(
                                    "failed to create {} sub-tree {} base-tree {}",
                                    tree_name, sub_index, base_index,
                                )
                            },
                        )
                    })
                    .collect();
                MerkleTreeWrapper::from_trees(base_trees).unwrap_or_else(|_| {
                    panic!(
                        "failed to create {} sub-tree {} from base-trees",
                        tree_name, sub_index,
                    )
                })
            })
            .collect();
        MerkleTreeWrapper::from_sub_trees(sub_trees)
            .unwrap_or_else(|_| panic!("failed to create {} from sub-trees", tree_name))
    }
}

fn get_apex_leafs(
    tree_d_new: &MerkleTreeWrapper<
        <TreeD as MerkleTreeTrait>::Hasher,
        <TreeD as MerkleTreeTrait>::Store,
        <TreeD as MerkleTreeTrait>::Arity,
        <TreeD as MerkleTreeTrait>::SubTreeArity,
        <TreeD as MerkleTreeTrait>::TopTreeArity,
    >,
    k: usize,
) -> Vec<TreeDDomain> {
    let sector_nodes = tree_d_new.leafs();
    let tree_d_height = sector_nodes.trailing_zeros() as usize;
    let partition_count = partition_count(sector_nodes);
    let partition_tree_height = partition_count.trailing_zeros() as usize;
    let apex_leafs_per_partition = apex_leaf_count(sector_nodes);
    let apex_tree_height = apex_leafs_per_partition.trailing_zeros() as usize;
    let apex_leafs_height = tree_d_height - partition_tree_height - apex_tree_height;

    let mut apex_leafs_start = sector_nodes;
    for i in 1..apex_leafs_height {
        apex_leafs_start += sector_nodes >> i;
    }
    apex_leafs_start += k * apex_leafs_per_partition;
    let apex_leafs_stop = apex_leafs_start + apex_leafs_per_partition;
    tree_d_new
        .read_range(apex_leafs_start, apex_leafs_stop)
        .unwrap_or_else(|_| {
            panic!(
                "failed to read tree_d_new apex-leafs (k={}, range={}..{})",
                k, apex_leafs_start, apex_leafs_stop,
            )
        })
}

fn encode_new_replica(
    labels_r_old: &[TreeRDomain],
    labels_d_new: &[TreeDDomain],
    phi: &TreeRDomain,
    h: usize,
) -> Vec<TreeRDomain> {
    let sector_nodes = labels_r_old.len();
    assert_eq!(sector_nodes, labels_d_new.len());

    let node_index_bit_len = sector_nodes.trailing_zeros() as usize;
    let partition_count = partition_count(sector_nodes);
    let partition_bit_len = partition_count.trailing_zeros() as usize;

    // The bit-length of a node-index after the partition bits have been stripped.
    let node_index_sans_partition_bit_len = node_index_bit_len - partition_bit_len;
    // Bitwise AND-mask which removes the partition bits from each node-index.
    let remove_partition_mask = (1 << node_index_sans_partition_bit_len) - 1;
    let get_high_bits_shr = node_index_sans_partition_bit_len - h;

    (0..sector_nodes)
        .map(|node| {
            // Remove the partition-index from the node-index then take the `h` high bits.
            let high: TreeRDomain = {
                let node_sans_partition = node & remove_partition_mask;
                let high = node_sans_partition >> get_high_bits_shr;
                Fr::from(high as u64).into()
            };

            // `rho = H(phi || high)`
            let rho: Fr = <TreeRHasher as Hasher>::Function::hash2(phi, &high).into();

            // `label_r_new = label_r_old + label_d_new * rho`
            let label_r_old: Fr = labels_r_old[node].into();
            let label_d_new: Fr = labels_d_new[node].into();
            (label_r_old + label_d_new * rho).into()
        })
        .collect()
}

fn test_empty_sector_update_circuit<TreeR>(sector_nodes: usize)
where
    TreeR: MerkleTreeTrait<Hasher = TreeRHasher>,
{
    validate_tree_r_shape::<TreeR>(sector_nodes);

    let sector_bytes = sector_nodes << 5;
    let hs = hs(sector_nodes);
    let h = hs[H_SELECT.trailing_zeros() as usize];

    let mut rng = XorShiftRng::from_seed(TEST_SEED);

    // Merkle tree storage directory.
    let tmp_dir = tempdir().unwrap();
    let tmp_path = tmp_dir.path();

    // Create random TreeROld.
    let labels_r_old: Vec<TreeRDomain> = (0..sector_nodes)
        .map(|_| TreeRDomain::random(&mut rng))
        .collect();
    let tree_r_old = create_tree::<TreeR>(&labels_r_old, tmp_path, "tree-r-old");
    let comm_r_last_old = tree_r_old.root();
    let comm_c = TreeRDomain::random(&mut rng);
    let comm_r_old = <TreeRHasher as Hasher>::Function::hash2(&comm_c, &comm_r_last_old);

    // Create random TreeDNew.
    let labels_d_new: Vec<TreeDDomain> = (0..sector_nodes)
        .map(|_| TreeDDomain::random(&mut rng))
        .collect();
    let tree_d_new = create_tree::<TreeD>(&labels_d_new, tmp_path, "tree-d-new");
    let comm_d_new = tree_d_new.root();

    // `phi = H(comm_d_new || comm_r_old)`
    let phi = <TreeRHasher as Hasher>::Function::hash2(&Fr::from(comm_d_new).into(), &comm_r_old);

    // Encode `labels_d_new` into `labels_r_new` and create TreeRNew.
    let labels_r_new = encode_new_replica(&labels_r_old, &labels_d_new, &phi, h);
    let tree_r_new = create_tree::<TreeR>(&labels_r_new, tmp_path, "tree-r-new");
    let comm_r_last_new = tree_r_new.root();
    let comm_r_new = <TreeRHasher as Hasher>::Function::hash2(&comm_c, &comm_r_last_new);

    let pub_params = PublicParams::from_sector_size(sector_bytes as u64);

    for k in 0..pub_params.partition_count {
        let pub_inputs = circuit::PublicInputs {
            k,
            comm_r_old,
            comm_d_new,
            comm_r_new,
            h_select: H_SELECT,
        };

        let apex_leafs: Vec<Option<Fr>> = get_apex_leafs(&tree_d_new, k)
            .into_iter()
            .map(|apex_leaf| Some(apex_leaf.into()))
            .collect();

        let challenge_proofs: Vec<circuit::ChallengeProof<TreeR>> =
            Challenges::new(sector_nodes, comm_r_new, k)
                .enumerate()
                .take(pub_params.challenge_count)
                .map(|(i, c)| {
                    let proof_r_old = tree_r_old.gen_proof(c).unwrap_or_else(|_| {
                        panic!("failed to generate `proof_r_old` for c_{}={}", i, c)
                    });
                    let proof_d_new = tree_d_new.gen_proof(c).unwrap_or_else(|_| {
                        panic!("failed to generate `proof_d_new` for c_{}={}", i, c)
                    });
                    let proof_r_new = tree_r_new.gen_proof(c).unwrap_or_else(|_| {
                        panic!("failed to generate `proof_r_new` for c_{}={}", i, c)
                    });

                    let path_r_old: Vec<Vec<Option<Fr>>> = proof_r_old
                        .path()
                        .into_iter()
                        .map(|(siblings, _insert)| {
                            siblings.into_iter().map(|s| Some(s.into())).collect()
                        })
                        .collect();
                    let path_d_new: Vec<Vec<Option<Fr>>> = proof_d_new
                        .path()
                        .into_iter()
                        .map(|(siblings, _insert)| {
                            siblings.into_iter().map(|s| Some(s.into())).collect()
                        })
                        .collect();
                    let path_r_new: Vec<Vec<Option<Fr>>> = proof_r_new
                        .path()
                        .into_iter()
                        .map(|(siblings, _insert)| {
                            siblings.into_iter().map(|s| Some(s.into())).collect()
                        })
                        .collect();

                    circuit::ChallengeProof {
                        leaf_r_old: Some(proof_r_old.leaf().into()),
                        path_r_old,
                        leaf_d_new: Some(proof_d_new.leaf().into()),
                        path_d_new,
                        leaf_r_new: Some(proof_r_new.leaf().into()),
                        path_r_new,
                        _tree_r: PhantomData,
                    }
                })
                .collect();

        let circuit = EmptySectorUpdateCircuit::<TreeR> {
            pub_params: pub_params.clone(),
            k: Some(Fr::from(pub_inputs.k as u64)),
            comm_r_old: Some(pub_inputs.comm_r_old.into()),
            comm_d_new: Some(pub_inputs.comm_d_new.into()),
            comm_r_new: Some(pub_inputs.comm_r_new.into()),
            h_select: Some(Fr::from(pub_inputs.h_select)),
            comm_c: Some(comm_c.into()),
            comm_r_last_old: Some(comm_r_last_old.into()),
            comm_r_last_new: Some(comm_r_last_new.into()),
            apex_leafs,
            challenge_proofs,
        };

        let mut cs = TestConstraintSystem::<Fr>::new();
        circuit.synthesize(&mut cs).expect("failed to synthesize");
        assert!(cs.is_satisfied());
        assert!(cs.verify(&pub_inputs.to_vec()));
    }
}

#[test]
fn test_empty_sector_update_circuit_1kib() {
    type TreeR = MerkleTreeWrapper<TreeRHasher, DiskStore<TreeRDomain>, U8, U4, U0>;
    test_empty_sector_update_circuit::<TreeR>(SECTOR_SIZE_1_KIB);
}

#[test]
fn test_empty_sector_update_circuit_2kib() {
    type TreeR = MerkleTreeWrapper<TreeRHasher, DiskStore<TreeRDomain>, U8, U0, U0>;
    test_empty_sector_update_circuit::<TreeR>(SECTOR_SIZE_2_KIB);
}

#[test]
fn test_empty_sector_update_circuit_4kib() {
    type TreeR = MerkleTreeWrapper<TreeRHasher, DiskStore<TreeRDomain>, U8, U2, U0>;
    test_empty_sector_update_circuit::<TreeR>(SECTOR_SIZE_4_KIB);
}

#[test]
fn test_empty_sector_update_circuit_8kib() {
    type TreeR = MerkleTreeWrapper<TreeRHasher, DiskStore<TreeRDomain>, U8, U4, U0>;
    test_empty_sector_update_circuit::<TreeR>(SECTOR_SIZE_8_KIB);
}

#[test]
fn test_empty_sector_update_circuit_16kib() {
    type TreeR = MerkleTreeWrapper<TreeRHasher, DiskStore<TreeRDomain>, U8, U8, U0>;
    test_empty_sector_update_circuit::<TreeR>(SECTOR_SIZE_16_KIB);
}

#[test]
fn test_empty_sector_update_circuit_32kib() {
    type TreeR = MerkleTreeWrapper<TreeRHasher, DiskStore<TreeRDomain>, U8, U8, U2>;
    test_empty_sector_update_circuit::<TreeR>(SECTOR_SIZE_32_KIB);
}
