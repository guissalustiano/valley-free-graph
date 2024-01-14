/// valley-free is a library that builds AS-level topology using CAIDA's
/// AS-relationship data file and run path exploration using valley-free routing
/// principle.
use std::{
    collections::{HashSet, VecDeque},
    convert::TryInto,
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

pub enum Direction {
    Up,
    Peer,
    Down,
}

pub type TopologyPath = Vec<u32>;

pub struct Topology(DiGraph<u32, RelType>);

#[derive(Debug)]
pub enum TopologyError {
    IoError(io::Error),
    ParseAsnError(std::num::ParseIntError),
    ParseError(String),
}

impl Topology {
    pub fn from_edges(edges: Vec<(u32, u32, RelType)>) -> Self {
        Topology(DiGraph::from_edges(edges))
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

    pub fn providers_of(&self, asn: u32) -> HashSet<u32> {
        let incoming = self
            .0
            .edges_directed(asn.into(), petgraph::Direction::Incoming)
            .filter(|edge| edge.weight() == &RelType::ProviderToCustomer) // could be PearToPear
            .map(|edge| self.asn_of(edge.source()));

        let outgoing = self
            .0
            .edges_directed(asn.into(), petgraph::Direction::Outgoing)
            .filter(|edge| edge.weight() == &RelType::CustomerToProvider)
            .map(|edge| self.asn_of(edge.target()));

        incoming.chain(outgoing).collect()
    }

    pub fn customers_of(&self, asn: u32) -> HashSet<u32> {
        let outgoing = self
            .0
            .edges_directed(asn.into(), petgraph::Direction::Outgoing)
            .filter(|edge| edge.weight() == &RelType::ProviderToCustomer) // could be PearToPear
            .map(|edge| self.asn_of(edge.target()));

        let incoming = self
            .0
            .edges_directed(asn.into(), petgraph::Direction::Incoming)
            .filter(|edge| edge.weight() == &RelType::CustomerToProvider)
            .map(|edge| self.asn_of(edge.source()));

        outgoing.chain(incoming).collect()
    }

    pub fn peers_of(&self, asn: u32) -> HashSet<u32> {
        let outgoing = self
            .0
            .edges_directed(asn.into(), petgraph::Direction::Outgoing)
            .filter(|edge| edge.weight() == &RelType::PearToPear)
            .map(|edge| self.asn_of(edge.target()));

        let incoming = self
            .0
            .edges_directed(asn.into(), petgraph::Direction::Incoming)
            .filter(|edge| edge.weight() == &RelType::PearToPear)
            .map(|edge| self.asn_of(edge.source()));

        outgoing.chain(incoming).collect()
    }

    fn asn_of(&self, asn: NodeIndex) -> u32 {
        asn.index().try_into().unwrap()
    }

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

    pub fn paths_graph(&self, asn: u32) -> DiGraph<u32, RelType> {
        let mut new_edges: Vec<(u32, u32, RelType)> = vec![];

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

                seen.insert(provider_asn);
                up_path_queue.push_back(provider_asn);
                new_edges.push((asn, provider_asn, RelType::CustomerToProvider));
            }
        }

        // Iterate over all ASes reach by UP
        // They can only do one PEAR, so we don't need a queue
        for asn in seen.clone().into_iter() {
            for peer_asn in self.peers_of(asn) {
                new_edges.push((asn.clone(), peer_asn, RelType::PearToPear));
                seen.insert(peer_asn);
            }
        }

        let mut down_path_queue = VecDeque::<u32>::new();
        for asn in seen.iter() {
            down_path_queue.push_back(asn.clone());
        }

        while !down_path_queue.is_empty() {
            let asn = down_path_queue.pop_front().unwrap();

            for customer_asn in self.customers_of(asn) {
                if seen.contains(&customer_asn) {
                    continue;
                }

                seen.insert(customer_asn);
                down_path_queue.push_back(customer_asn);
                new_edges.push((asn, customer_asn, RelType::ProviderToCustomer));
            }
        }

        DiGraph::from_edges(new_edges)
    }
}

#[cfg(test)]
mod test {
    use std::fs::File;

    use bzip2::read::BzDecoder;

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
    fn test_asn_of() {
        let topo = Topology::from_edges(vec![(1, 2, RelType::ProviderToCustomer)]);

        assert_eq!(topo.asn_of(1.into()), 1);
        assert_eq!(topo.asn_of(2.into()), 2);
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
    fn test_topology_from() {}
}
