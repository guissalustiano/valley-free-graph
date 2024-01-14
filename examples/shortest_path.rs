use std::fs::File;

use petgraph::algo::astar;
use valley_free_graph::Topology;

fn main() {
    let file = File::open("20231201.as-rel.txt").unwrap();
    let topo = Topology::from_caida(file).unwrap();

    let university_of_twente_asn = 1133;
    let universidade_de_sao_paulo_asn = 28571;
    let ut_path = topo.paths_graph(university_of_twente_asn);

    // Use A* to find the shortest path between two nodes
    let (_len, path) = astar(
        ut_path.raw_graph(),
        ut_path.index_of(university_of_twente_asn),
        |finish| finish == ut_path.index_of(universidade_de_sao_paulo_asn),
        |edge| match edge.weight() {
            // priorize pearing
            valley_free_graph::RelType::PearToPear => 0,
            valley_free_graph::RelType::ProviderToCustomer => 1,
            valley_free_graph::RelType::CustomerToProvider => 2,
        },
        |_| 0,
    )
    .unwrap();
    let path = path
        .iter()
        .map(|node| ut_path.asn_of(*node))
        .collect::<Vec<_>>();

    println!("Path from UT to USP: {:?}", path);
}
