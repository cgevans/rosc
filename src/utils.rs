use std::{net, num};

fn parse_ip_v4(raw_addr: &str) -> Result<net::Ipv4Addr, String> {
    let octets: Vec<u8> = raw_addr.splitn(4, '.')
                                  .map(|octet| octet.parse::<u8>())
                                  .filter_map(|octet| {
                                      if octet.is_ok() {
                                          octet.ok()
                                      } else {
                                          None
                                      }
                                  })
                                  .collect();

    if octets.len() < 4 {
        Err(format!("There was an error parsing the IPv4 address: {}", raw_addr))
    } else {
        Ok(net::Ipv4Addr::new(octets[0], octets[1], octets[2], octets[3]))
    }
}

fn parse_port(raw_port: &str) -> Result<u16, num::ParseIntError> {
    raw_port.parse()
}

pub fn parse_ip_and_port(raw_addr: &String) -> Result<(net::Ipv4Addr, u16), String> {
    let parts: Vec<&str> = raw_addr.splitn(2, ':').collect();
    match parts.len() {
        2 => {
            let ip: Result<net::Ipv4Addr, String> = parse_ip_v4(parts[0]);
            let port: Result<u16, num::ParseIntError> = parse_port(parts[1]);
            match ip {
                Ok(ip) => {
                    match port {
                        Ok(port) => Ok((ip, port)),
                        Err(e) => Err(format!("Bad port value: {}", e)),
                    }
                }
                Err(e) => Err(format!("Bad IPv4 address: {}", e)),
            }
        }
        _ => Err(format!("Bad address: {}, Missing port?", raw_addr)),
    }
}