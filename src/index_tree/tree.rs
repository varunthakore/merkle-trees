use neptune::poseidon::PoseidonConstants;
use neptune::sponge::vanilla::{Sponge, SpongeTrait};
use neptune::{Arity, Strength};

use ff::{PrimeField, PrimeFieldBits};

use std::cmp::PartialOrd;
use std::collections::HashMap;
use std::marker::PhantomData;

use crate::hash::vanilla::hash;

#[derive(Debug, Clone)]
pub struct Leaf<F: PrimeField + PrimeFieldBits, A: Arity<F>> {
    pub value: Option<F>,
    pub next_value: Option<F>,
    pub next_index: Option<F>,
    pub _arity: PhantomData<A>,
}

impl<F: PrimeField + PrimeFieldBits, A: Arity<F>> Default for Leaf<F, A> {
    fn default() -> Self {
        Self {
            value: Some(F::ZERO),
            next_value: Some(F::ZERO),
            next_index: Some(F::ZERO),
            _arity: PhantomData,
        }
    }
}

impl<F, A> Leaf<F, A>
where
    F: PrimeField + PrimeFieldBits,
    A: Arity<F>,
{
    pub fn leaf_to_vec(&self) -> Vec<F> {
        let mut input: Vec<F> = vec![];
        input.push(self.value.unwrap());
        input.push(self.next_value.unwrap());
        input.push(self.next_index.unwrap());

        assert_eq!(input.len(), 3);
        // input = [value, next_value, next_index]
        input
    }

    pub fn hash_leaf(&self, p: &PoseidonConstants<F, A>) -> F {
        let input = self.leaf_to_vec();
        hash::<F, A>(input, p)
    }
}

#[derive(Clone, Debug)]
pub struct IndexTree<F: PrimeField + PrimeFieldBits, const N: usize, AL: Arity<F>, AN: Arity<F>> {
    pub root: F,
    pub hash_db: HashMap<String, (F, F)>,
    pub inserted_leaves: Vec<Leaf<F, AL>>,
    pub next_insertion_idx: F,
    pub leaf_hash_params: PoseidonConstants<F, AL>,
    pub node_hash_params: PoseidonConstants<F, AN>,
}

impl<F: PrimeField + PrimeFieldBits + PartialOrd, const N: usize, AL: Arity<F>, AN: Arity<F>> IndexTree<F, N, AL, AN> {
    // Create a new tree. `empty_leaf_val` is the default value for leaf of empty tree.
    pub fn new(empty_leaf_val: Leaf<F, AL>) -> IndexTree<F, N, AL, AN> {
        assert!(N > 0);
        let mut hash_db = HashMap::<String, (F, F)>::new();
        let leaf_hash_params = Sponge::<F, AL>::api_constants(Strength::Standard);
        let node_hash_params = Sponge::<F, AN>::api_constants(Strength::Standard);
        let mut cur_hash = Leaf::<F, AL>::hash_leaf(&empty_leaf_val, &leaf_hash_params);
        for _ in 0..N {
            let val = (cur_hash.clone(), cur_hash.clone());
            cur_hash = hash(vec![cur_hash.clone(), cur_hash.clone()], &node_hash_params);
            hash_db.insert(format!("{:?}", cur_hash.clone()), val);
        }
        let inserted_leaves: Vec<Leaf<F, AL>> = vec![empty_leaf_val];
        let next_insertion_index = F::ONE;

        Self {
            root: cur_hash,
            hash_db: hash_db,
            inserted_leaves: inserted_leaves,
            next_insertion_idx: next_insertion_index,
            leaf_hash_params: leaf_hash_params,
            node_hash_params: node_hash_params,
        }
    }

    pub fn insert_vanilla(&mut self, new_val: F) {
        // Check that leaf at next_insertion_index is empty
        let next_leaf_idx = idx_to_bits(N, self.next_insertion_idx);
        let empty_path = self.get_siblings_path(next_leaf_idx.clone());
        assert!(empty_path.is_member_vanilla(next_leaf_idx.clone(), &Leaf::default(), self.root));

        // Get low leaf
        let (mut low_leaf, low_index_int) = self.get_low_leaf(Some(new_val));
        let low_index = F::from(low_index_int);
        let mut low_leaf_idx = idx_to_bits(N, low_index);

        // Check that low leaf is member
        let low_leaf_path = self.get_siblings_path(low_leaf_idx.clone());
        assert!(low_leaf_path.is_member_vanilla(low_leaf_idx.clone(), &low_leaf, self.root));

        // Range check low leaf against new value
        assert!(new_val < low_leaf.next_value.unwrap() || low_leaf.next_value.unwrap() == F::ZERO);
        assert!(new_val > low_leaf.value.unwrap());

        // Update new leaf pointers
        let new_leaf = Leaf {
            value: Some(new_val),
            next_value: low_leaf.next_value,
            next_index: low_leaf.next_index,
            _arity: PhantomData::<AL>,
        };

        // Update low leaf pointers
        low_leaf.next_index = Some(self.next_insertion_idx);
        low_leaf.next_value = new_leaf.value;

        // Insert new low leaf into tree
        let mut low_leaf_siblings = low_leaf_path.siblings;
        low_leaf_idx.reverse(); // Reverse since path was from root to leaf but I am going leaf to root
        let mut cur_low_leaf_hash = Leaf::<F, AL>::hash_leaf(&low_leaf, &self.leaf_hash_params);
        for d in low_leaf_idx {
            let sibling = low_leaf_siblings.pop().unwrap();
            let (l, r) = if d == false {
                // leaf falls on the left side
                (cur_low_leaf_hash, sibling)
            } else {
                // leaf falls on the right side
                (sibling, cur_low_leaf_hash)
            };
            let val = (l, r);
            cur_low_leaf_hash = hash(vec![l.clone(), r.clone()], &self.node_hash_params);
            self.hash_db
                .insert(format!("{:?}", cur_low_leaf_hash.clone()), val);
        }
        self.root = cur_low_leaf_hash;
        self.inserted_leaves[low_index_int as usize] = low_leaf.clone(); // Update the low_leaf in inserted leaves

        // Insert new leaf into tree
        let mut new_leaf_idx = idx_to_bits(N, self.next_insertion_idx); // from root to leaf
        let mut new_leaf_siblings = self.get_siblings_path(new_leaf_idx.clone()).siblings;
        new_leaf_idx.reverse(); // from leaf to root
        let mut cur_new_leaf_hash = Leaf::<F, AL>::hash_leaf(&new_leaf, &self.leaf_hash_params);
        for d in new_leaf_idx {
            let sibling = new_leaf_siblings.pop().unwrap();
            let (l, r) = if d == false {
                // leaf falls on the left side
                (cur_new_leaf_hash, sibling)
            } else {
                // leaf falls on the right side
                (sibling, cur_new_leaf_hash)
            };
            let val = (l, r);
            cur_new_leaf_hash = hash(vec![l.clone(), r.clone()], &self.node_hash_params);
            self.hash_db
                .insert(format!("{:?}", cur_new_leaf_hash.clone()), val);
        }
        self.next_insertion_idx += F::ONE;
        self.root = cur_new_leaf_hash;
        self.inserted_leaves.push(new_leaf); // Push the new lead to inserted leaf
    }

    // Check that there is no Leaf with value = new_value in the tree
    pub fn is_non_member_vanilla(
        &self,
        new_value: F,
    ) -> bool {
        // Check that low leaf is memeber, self is siblings path for low_leaf
        let (low_leaf, low_int) = self.get_low_leaf(Some(new_value));
        let low_leaf_idx = idx_to_bits(N, F::from(low_int));
        let low_path = self.get_siblings_path(low_leaf_idx.clone());
        assert!(low_path.is_member_vanilla(low_leaf_idx.clone(), &low_leaf, self.root));

        // Range check low leaf against new value
        if low_leaf.next_index == Some(F::ZERO) {
            return low_leaf.value < Some(new_value); // the low leaf is at the very end, so the new_value must be higher than all values in the tree
        } else {
            return low_leaf.value < Some(new_value) && low_leaf.next_value > Some(new_value);
        }
    }

    // Get siblings given leaf index
    pub fn get_siblings_path(
        &self,
        idx_in_bits: Vec<bool>, // root to leaf
    ) -> Path<F, N, AL, AN> {
        let mut cur_node = self.root;
        let mut siblings = Vec::<F>::new();

        let mut children;
        for d in idx_in_bits {
            children = self
                .hash_db
                .get(&format!("{:?}", cur_node.clone()))
                .unwrap();
            if d == false {
                // leaf falls on the left side
                cur_node = children.0;
                siblings.push(children.1);
            } else {
                // leaf falls on the right side
                cur_node = children.1;
                siblings.push(children.0);
            }
        }

        Path {
            siblings: siblings, // siblings from root to leaf
            leaf_hash_params: self.leaf_hash_params.clone(),
            node_hash_params: self.node_hash_params.clone(),
        }
    }

    pub fn get_low_leaf(&self, new_value: Option<F>) -> (Leaf<F, AL>, u64) {

        match new_value {
            Some(new_value) => {
                let mut low_leaf = Leaf::default();
                let mut low_index = 0;
                for (i, leaf) in self.inserted_leaves.iter().enumerate() {
                    if leaf.value.unwrap() < new_value && (leaf.next_value.unwrap() >= new_value || leaf.next_value.unwrap() == F::ZERO)
                    {
                        low_leaf = leaf.clone();
                        low_index = i as u64;
                        break;
                    }
                }
                (low_leaf, low_index)
            }
            None => {
                let low_leaf = Leaf {
                    value: None,
                    next_index: None,
                    next_value: None,
                    _arity: PhantomData
                };
                (low_leaf, 0u64)
            }
        }

    }
}

pub fn idx_to_bits<F: PrimeField + PrimeFieldBits>(depth: usize, idx: F) -> Vec<bool> {
    let mut path: Vec<bool> = vec![];
    for d in idx.to_le_bits() {
        if path.len() >= depth {
            break;
        }

        if d == true {
            path.push(true)
        } else {
            path.push(false)
        }
    }

    while path.len() != depth {
        path.push(false);
    }

    path.reverse();
    path // path is from root to leaf
}

#[derive(Clone)]
pub struct Path<F, const N: usize, AL, AN>
where
    F: PrimeField + PrimeFieldBits,
    AL: Arity<F>, 
    AN: Arity<F>,
{
    pub siblings: Vec<F>, // siblings from root to leaf
    pub leaf_hash_params: PoseidonConstants<F, AL>,
    pub node_hash_params: PoseidonConstants<F, AN>,
}

impl<F: PrimeField + PrimeFieldBits + PartialOrd, const N: usize, AL: Arity<F>, AN: Arity<F>> Path<F, N, AL, AN> {
    pub fn compute_root(&self, mut idx_in_bits: Vec<bool>, val: &Leaf<F, AL>) -> F {
        assert_eq!(self.siblings.len(), N);
        idx_in_bits.reverse(); // from leaf to root

        let mut cur_hash = Leaf::<F, AL>::hash_leaf(val, &self.leaf_hash_params);

        for (i, sibling) in self.siblings.clone().into_iter().rev().enumerate() {
            let (l, r) = if idx_in_bits[i] == false {
                // leaf falls on the left side
                (cur_hash, sibling)
            } else {
                // leaf falls on the right side
                (sibling, cur_hash)
            };
            cur_hash = hash(vec![l.clone(), r.clone()], &self.node_hash_params);
        }
        cur_hash
    }

    // Check that Leaf is present in the tree
    pub fn is_member_vanilla(
        &self,
        idx_in_bits: Vec<bool>, // from root to leaf
        leaf: &Leaf<F, AL>,
        root: F,
    ) -> bool {
        let computed_root = self.compute_root(idx_in_bits, &leaf);
        computed_root == root
    }
}

#[cfg(test)]
mod tests {
    use super::Leaf;
    use super::*;
    use crate::index_tree::tree::IndexTree;
    use generic_array::typenum::{U3, U2};
    use pasta_curves::group::ff::Field;
    use pasta_curves::pallas::Base as Fp;
    use std::marker::PhantomData;

    #[test]
    fn test_vanilla() {
        let mut rng = rand::thread_rng();
        const HEIGHT: usize = 32;
        let empty_leaf = Leaf::default();
        let mut tree: IndexTree<Fp, HEIGHT, U3, U2> = IndexTree::new(empty_leaf.clone());

        let num_values = 100;
        let values: Vec<Fp> = (0..num_values).map(|_| Fp::random(&mut rng)).collect();

        for new_value in values {
            let next_leaf_idx = idx_to_bits(HEIGHT, tree.next_insertion_idx);
            let (low_leaf, _) = tree.get_low_leaf(Some(new_value));

            let new_leaf = Leaf {
                value: Some(new_value),
                next_value: low_leaf.next_value,
                next_index: low_leaf.next_index,
                _arity: PhantomData::<U3>,
            };

            // Before inserting, is_member should fail
            let inserted_path = tree.get_siblings_path(next_leaf_idx.clone());
            assert!(!inserted_path.is_member_vanilla(
                next_leaf_idx.clone(),
                &new_leaf.clone(),
                tree.root
            ));
            // Before inserting, is_non_member should pass
            assert!(tree.is_non_member_vanilla(new_value));

            // Insert new value at next_insertion_index
            tree.insert_vanilla(new_value);

            // Check that new leaf is inseted at next_insertion_index
            let inserted_path = tree.get_siblings_path(next_leaf_idx.clone());
            assert!(inserted_path.is_member_vanilla(
                next_leaf_idx.clone(),
                &new_leaf.clone(),
                tree.root
            ));

            // After inserting, is_non_member should fail
            assert!(!tree.is_non_member_vanilla(new_value));
        }
    }
}
