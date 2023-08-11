# Merkle Trees
This repository contains implementation of the following Merkle Trees along with R1CS circuits implemented using [bellperson](https://github.com/filecoin-project/bellperson) (Filecoin's fork of [bellman](https://github.com/zkcrypto/bellman)).

1. **Vanilla Merkle Tree** - circuit to verify membership 
2. **Indexed Merkle Tree** - circuit for insertion, checking membership and checking non-membership

All the trees use Poseidon hash function implemented by [Neptune](https://github.com/lurk-lab/neptune).

## References
1. [Indexed Merkle Tree](https://docs.aztec.network/aztec/protocol/trees/indexed-merkle-tree)
