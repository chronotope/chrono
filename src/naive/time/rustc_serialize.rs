#![cfg_attr(docsrs, doc(cfg(feature = "rustc-serialize")))]

use super::NaiveTime;
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};

impl Encodable for NaiveTime {
    fn encode<S: Encoder>(&self, s: &mut S) -> Result<(), S::Error> {
        format!("{:?}", self).encode(s)
    }
}

impl Decodable for NaiveTime {
    fn decode<D: Decoder>(d: &mut D) -> Result<NaiveTime, D::Error> {
        d.read_str()?.parse().map_err(|_| d.error("invalid time"))
    }
}

#[cfg(test)]
mod tests {
    use crate::naive::time::{test_decodable_json, test_encodable_json};
    use rustc_serialize::json;

    #[test]
    fn test_encodable() {
        test_encodable_json(json::encode);
    }

    #[test]
    fn test_decodable() {
        test_decodable_json(json::decode);
    }
}
