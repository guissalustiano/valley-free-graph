/// valley-free is a library that builds AS-level topology using CAIDA's
/// AS-relationship data file and run path exploration using valley-free routing
/// principle.
use std::{
    collections::{HashMap, HashSet, VecDeque},
    io,
};

use petgraph::{
    graph::{DiGraph, NodeIndex},
    visit::EdgeRef,
};

#[derive(Debug, PartialEq, Eq, Hash, Copy, Clone)]
pub enum RelType {
    ProviderToCustomer,
    PearToPear,
    CustomerToProvider,
}

// Required to work as a edge
impl Default for RelType {
    fn default() -> Self {
        RelType::ProviderToCustomer
    }
}

pub trait TopologyExt {
    fn all_asns(&self) -> HashSet<u32>;
    fn asn_of(&self, asn: NodeIndex) -> u32;
    fn providers_of(&self, asn: u32) -> HashSet<u32>;
    fn customers_of(&self, asn: u32) -> HashSet<u32>;
    fn peers_of(&self, asn: u32) -> HashSet<u32>;

    /*
     * Given the following topology:
     *
     *               ┌─────┐
     *               │     │
     *               └──┬──┘
     *           ┌──────┴─────┐
     *        ┌──▼──┐      ┌──▼──┐
     *        │     ◄──────►     │
     *        └──┬──┘      └──┬──┘
     *     ┌─────┴────┐  ┌────┴────┐
     *  ┌──▼──┐     ┌─▼──▼┐     ┌──▼──┐
     *  │     │     │     │     │     │
     *  └─────┘     └─────┘     └─────┘
     *
     *  This method generate a DAG with all paths from the given AS to all other AS-relationship
     *  following the valley-free principle.
     *
     *              ┌─────┐
     *              │     │
     *              └──▲──┘
     *          ┌──────┴─────┐
     *       ┌──┴──┐      ┌──▼──┐
     *       │     ├──────►     │
     *       └──▲──┘      └──┬──┘
     *    ┌─────┴────┐  ┌────┴────┐
     * ┌──┴──┐     ┌─▼──▼┐     ┌──▼──┐
     * │     │     │     │     │     │
     * └─────┘     └─────┘     └─────┘
     *
     * You can use this graph to calculate the shortest path or even list all paths using the
     * petgraph library.
     */
    fn paths_graph(&self, asn: u32) -> DiGraph<u32, RelType> {
        let mut graph = DiGraph::new();

        let node_map: HashMap<u32, NodeIndex> = self
            .all_asns()
            .into_iter()
            .map(|asn| (asn, graph.add_node(asn)))
            .collect();

        let mut up_path_queue = VecDeque::<u32>::new();
        let mut seen = HashSet::new();

        // add first
        up_path_queue.push_back(asn);
        seen.insert(asn);

        while !up_path_queue.is_empty() {
            let asn = up_path_queue.pop_front().unwrap(); // While check if has elements

            for provider_asn in self.providers_of(asn) {
                if seen.contains(&provider_asn) {
                    continue;
                }
                dbg!(asn, provider_asn);

                seen.insert(provider_asn);
                up_path_queue.push_back(provider_asn);
                graph.add_edge(
                    *node_map.get(&asn).unwrap(),
                    *node_map.get(&provider_asn).unwrap(),
                    RelType::CustomerToProvider,
                );
            }
        }

        // Iterate over all ASes reach by UP
        // They can only do one PEAR, so we don't need a queue
        for asn in seen.clone().into_iter() {
            for peer_asn in self.peers_of(asn) {
                seen.insert(peer_asn);
                graph.add_edge(
                    *node_map.get(&asn).unwrap(),
                    *node_map.get(&peer_asn).unwrap(),
                    RelType::PearToPear,
                );
            }
        }

        let mut down_path_queue = VecDeque::<u32>::new();
        for asn in seen.iter() {
            down_path_queue.push_back(*asn);
        }

        while !down_path_queue.is_empty() {
            let asn = down_path_queue.pop_front().unwrap();

            for customer_asn in self.customers_of(asn) {
                if seen.contains(&customer_asn) {
                    continue;
                }

                seen.insert(customer_asn);
                down_path_queue.push_back(customer_asn);
                graph.add_edge(
                    *node_map.get(&asn).unwrap(),
                    *node_map.get(&customer_asn).unwrap(),
                    RelType::ProviderToCustomer,
                );
            }
        }

        graph
    }
}

impl TopologyExt for DiGraph<u32, RelType> {
    fn all_asns(&self) -> HashSet<u32> {
        self.raw_nodes()
            .iter()
            .skip(1) // skip the first node, which is the root
            .map(|node| node.weight)
            .collect()
    }

    fn asn_of(&self, asn: NodeIndex) -> u32 {
        *self.node_weight(asn).unwrap()
    }

    fn providers_of(&self, asn: u32) -> HashSet<u32> {
        let incoming = self
            .edges_directed(asn.into(), petgraph::Direction::Incoming)
            .filter(|edge| edge.weight() == &RelType::ProviderToCustomer) // could be PearToPear
            .map(|edge| edge.source());

        let outgoing = self
            .edges_directed(asn.into(), petgraph::Direction::Outgoing)
            .filter(|edge| edge.weight() == &RelType::CustomerToProvider)
            .map(|edge| edge.target());

        incoming
            .chain(outgoing)
            .map(|asn| self.asn_of(asn))
            .collect()
    }

    fn customers_of(&self, asn: u32) -> HashSet<u32> {
        let outgoing = self
            .edges_directed(asn.into(), petgraph::Direction::Outgoing)
            .filter(|edge| edge.weight() == &RelType::ProviderToCustomer) // could be PearToPear
            .map(|edge| edge.target());

        let incoming = self
            .edges_directed(asn.into(), petgraph::Direction::Incoming)
            .filter(|edge| edge.weight() == &RelType::CustomerToProvider)
            .map(|edge| edge.source());

        outgoing
            .chain(incoming)
            .map(|asn| self.asn_of(asn))
            .collect()
    }

    fn peers_of(&self, asn: u32) -> HashSet<u32> {
        let outgoing = self
            .edges_directed(asn.into(), petgraph::Direction::Outgoing)
            .filter(|edge| edge.weight() == &RelType::PearToPear)
            .map(|edge| edge.target());

        let incoming = self
            .edges_directed(asn.into(), petgraph::Direction::Incoming)
            .filter(|edge| edge.weight() == &RelType::PearToPear)
            .map(|edge| edge.source());

        outgoing
            .chain(incoming)
            .map(|asn| self.asn_of(asn))
            .collect()
    }
}

pub struct Topology(DiGraph<u32, RelType>);

#[derive(Debug)]
pub enum TopologyError {
    IoError(io::Error),
    ParseAsnError(std::num::ParseIntError),
    ParseError(String),
}

impl Topology {
    pub fn from_edges(edges: Vec<(u32, u32, RelType)>) -> Self {
        let nodes = edges
            .iter()
            .flat_map(|(asn1, asn2, _)| vec![*asn1, *asn2])
            .collect::<HashSet<u32>>();

        // create node with defaul value (0)
        let mut graph = DiGraph::from_edges(edges);

        // fix node values
        for node in nodes {
            let node_weights = graph.node_weight_mut(node.into()).unwrap();
            *node_weights = node;
        }

        Topology(graph)
    }

    pub fn from_caida(reader: impl std::io::Read) -> Result<Self, TopologyError> {
        let content = reader
            .bytes()
            .collect::<Result<Vec<u8>, _>>()
            .map_err(TopologyError::IoError)?;

        let content = String::from_utf8(content).map_err(|e| {
            TopologyError::ParseError(format!("invalid UTF-8 in AS relationship file: {}", e))
        })?;

        let edges = content
            .lines()
            .filter(|line| !line.starts_with("#"))
            .map(|line| {
                let fields = line.split("|").collect::<Vec<&str>>();
                let asn1 = fields[0]
                    .parse::<u32>()
                    .map_err(TopologyError::ParseAsnError)?;
                let asn2 = fields[1]
                    .parse::<u32>()
                    .map_err(TopologyError::ParseAsnError)?;
                let rel = fields[2]
                    .parse::<i32>()
                    .map_err(TopologyError::ParseAsnError)?;

                match rel {
                    // asn1 and asn2 are peers
                    0 => Ok((asn1, asn2, RelType::PearToPear)),

                    // asn1 is a provider of asn2
                    -1 => Ok((asn1, asn2, RelType::ProviderToCustomer)),

                    _ => Err(TopologyError::ParseError(format!(
                        "unknown relationship type {} in {}",
                        rel, line
                    ))),
                }
            })
            .collect::<Result<Vec<(u32, u32, RelType)>, _>>()?;

        Ok(Topology::from_edges(edges))
    }

    fn asn_of(&self, asn: NodeIndex) -> u32 {
        *self.0.node_weight(asn).unwrap()
    }

    pub fn all_asns(&self) -> HashSet<u32> {
        self.0
            .raw_nodes()
            .iter()
            .skip(1) // skip the first node, which is the root
            .map(|node| node.weight)
            .collect()
    }

    pub fn providers_of(&self, asn: u32) -> HashSet<u32> {
        self.0.providers_of(asn.into())
    }

    pub fn customers_of(&self, asn: u32) -> HashSet<u32> {
        self.0.customers_of(asn.into())
    }

    pub fn peers_of(&self, asn: u32) -> HashSet<u32> {
        self.0.peers_of(asn.into())
    }

    pub fn paths_graph(&self, asn: u32) -> DiGraph<u32, RelType> {
        self.0.paths_graph(asn.into())
    }

    pub fn raw_graph(&self) -> &DiGraph<u32, RelType> {
        &self.0
    }
}

#[cfg(test)]
mod test {
    use std::fs::File;

    use bzip2::read::BzDecoder;
    use petgraph::dot::Dot;

    use super::*;

    /*
     *       ┌───────┐
     *       │   1   │
     *       └───┬───┘
     *     ┌─────┴─────┐
     * ┌───▼───┐   ┌───▼───┐
     * │   2   │   │   3   │
     * └───┬───┘   └───┬───┘
     *     └─────┬─────┘
     *       ┌───▼───┐
     *       │   4   │
     *       └───────┘
     */
    fn diamond_topology() -> Topology {
        Topology::from_edges(vec![
            (1, 2, RelType::ProviderToCustomer),
            (1, 3, RelType::ProviderToCustomer),
            (3, 2, RelType::PearToPear),
            (3, 4, RelType::ProviderToCustomer),
            (2, 4, RelType::ProviderToCustomer),
        ])
    }

    #[test]
    fn test_asn_of() {
        let topo = Topology::from_edges(vec![(1, 2, RelType::ProviderToCustomer)]);

        assert_eq!(topo.asn_of(1.into()), 1);
        assert_eq!(topo.asn_of(2.into()), 2);
    }

    #[test]
    fn test_all_asns() {
        let topo = diamond_topology();

        assert_eq!(topo.all_asns(), [1, 2, 3, 4].into());
    }

    #[test]
    fn test_providers() {
        let topo = diamond_topology();

        assert_eq!(topo.providers_of(1), [].into());
        assert_eq!(topo.providers_of(2), [1].into());
        assert_eq!(topo.providers_of(3), [1].into());
        assert_eq!(topo.providers_of(4), [2, 3].into());
    }

    #[test]
    fn test_customers() {
        let topo = diamond_topology();

        assert_eq!(topo.customers_of(1), [3, 2].into());
        assert_eq!(topo.customers_of(2), [4].into());
        assert_eq!(topo.customers_of(3), [4].into());
        assert_eq!(topo.customers_of(4), [].into());
    }

    #[test]
    fn test_peers() {
        let topo = diamond_topology();

        assert_eq!(topo.peers_of(1), [].into());
        assert_eq!(topo.peers_of(2), [3].into());
        assert_eq!(topo.peers_of(3), [2].into());
        assert_eq!(topo.peers_of(4), [].into());
    }

    #[test]
    fn test_from_caida() {
        let test_rel = r#"# xxx
1|2|-1
1|3|-1
2|4|-1
3|4|-1"#;
        let topo = Topology::from_caida(test_rel.as_bytes());

        assert!(topo.is_ok());
    }

    #[test]
    fn test_from_real_caida_data() {
        let file = File::open("20231201.as-rel.txt.bz2").unwrap();
        let reader = BzDecoder::new(&file);
        let topo = Topology::from_caida(reader);

        assert!(topo.is_ok());
    }

    #[test]
    /* Input:
     *               ┌─────┐
     *               │  1  │
     *               └──┬──┘
     *           ┌──────┴─────┐
     *        ┌──▼──┐      ┌──▼──┐
     *        │  2  ◄──────►  3  │
     *        └──┬──┘      └──┬──┘
     *     ┌─────┴────┐  ┌────┴────┐
     *  ┌──▼──┐     ┌─▼──▼─┐    ┌──▼──┐
     *  │  4  │     │  05  │    │  6  │
     *  └─────┘     └──────┘    └─────┘
     *
     * Expected output:
     *               ┌─────┐
     *               │  1  │
     *               └──▲──┘
     *           ┌──────┴─────┐
     *        ┌──┴──┐      ┌──▼──┐
     *        │  2  ├──────►  3  │
     *        └──▲──┘      └──┬──┘
     *     ┌─────┴────┐  ┌────┴────┐
     *  ┌──┴──┐     ┌─▼──▼─┐    ┌──▼──┐
     *  │  4  │     │  05  │    │  6  │
     *  └─────┘     └──────┘    └─────┘
     *
     */
    fn test_path_graph() {
        let topo = Topology::from_edges(vec![
            (1, 2, RelType::ProviderToCustomer),
            (1, 3, RelType::ProviderToCustomer),
            (2, 4, RelType::ProviderToCustomer),
            (2, 5, RelType::ProviderToCustomer),
            (2, 3, RelType::PearToPear),
            (3, 5, RelType::ProviderToCustomer),
            (3, 6, RelType::ProviderToCustomer),
        ]);
        println!("{:?}", Dot::new(topo.raw_graph()));

        let graph = topo.paths_graph(4);

        let has_edge = |asn1: u32, asn2: u32| graph.find_edge(asn1.into(), asn2.into()).is_some();

        println!("{:?}", Dot::new(&graph));

        assert!(has_edge(4, 2));
        assert!(has_edge(2, 1));
        assert!(has_edge(1, 3));
        assert!(has_edge(2, 3));
        assert!(has_edge(2, 5));
        assert!(has_edge(3, 5));
        assert!(has_edge(3, 6));
        assert_eq!(graph.edge_count(), 7);
    }
}
