use std::fs::File;

use valley_free_graph::Topology;

fn main() {
    let file = File::open("20231201.as-rel.txt").unwrap();
    let topo = Topology::from_caida(file).unwrap();

    println!("Number of ases: {}", topo.raw_graph().node_count());
}
