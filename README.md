# Valley Free Graph
`valley-free-graph` crate is a Rust package parse CAIDA's AS-relationship
into a graph allowing you to use all [petgraph](https://docs.rs/petgraph/latest/petgraph/index.html) methods.

It generate the paths graph with the rigth direction from one AS following the 
valley free model so you can find the [lenth of all sortest path](https://docs.rs/petgraph/latest/petgraph/algo/k_shortest_path/fn.k_shortest_path.html),
or even [all the paths](https://docs.rs/petgraph/latest/petgraph/algo/simple_paths/fn.all_simple_paths.html)
using classics graph algorithm.

## Examples
To use the examples expect the [CAIDA-as 2023-12-01 dataset](https://publicdata.caida.org/datasets/as-relationships/serial-1/20231201.as-rel.txt.bz2)
on root directory.

The examples are avaliable in the [`examples/`](examples/) direction.

## References
This library is higher inspired by [valley-free from bgpkit](https://github.com/bgpkit/valley-free),
but try to instead return a subset of all paths, return the whole graph and you do what you want with 
that using all the power of graph libraries.
