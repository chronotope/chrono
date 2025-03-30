use crate::{NaiveTime, ParseError};
use bincode::{
    BorrowDecode, Decode, Encode,
    de::{BorrowDecoder, Decoder},
    enc::Encoder,
    error::{DecodeError, EncodeError},
};

impl Encode for NaiveTime {
    fn encode<E: Encoder>(&self, encoder: &mut E) -> Result<(), EncodeError> {
        let v = self.to_string();

        <String>::encode(&v, encoder)
    }
}

impl<Context> Decode<Context> for NaiveTime {
    fn decode<D: Decoder<Context = Context>>(decoder: &mut D) -> Result<Self, DecodeError> {
        let value = <String>::decode(decoder)?;

        Ok(value.parse().map_err(|e: ParseError| DecodeError::OtherString(e.to_string()))?)
    }
}
impl<'de, Context> BorrowDecode<'de, Context> for NaiveTime {
    fn borrow_decode<D: BorrowDecoder<'de, Context = Context>>(
        decoder: &mut D,
    ) -> Result<Self, DecodeError> {
        let value = <String>::borrow_decode(decoder)?;

        Ok(value.parse().map_err(|e: ParseError| DecodeError::OtherString(e.to_string()))?)
    }
}

#[cfg(test)]
mod tests {
    use crate::{NaiveTime, Utc};
    use bincode::config;

    #[test]
    fn backward_compatibility_with_bincode_v1() {
        let initial_value = Utc::now().time();

        let legacy_bytes = bincode_v1::serialize(&initial_value)
            .expect(&format!("Bincode v1 should have been able to encode NaiveTime."));
        let (decoded, _) =
            bincode::decode_from_slice::<NaiveTime, _>(&legacy_bytes, config::legacy())
                .expect(&format!("Bincode v2 should have been able to decode legacy bytes."));
        assert_eq!(initial_value, decoded);

        let new_bytes = bincode::encode_to_vec(&decoded, config::legacy())
            .expect("Bincode v2 should have been able to encode NaiveTime using legacy config.");
        let decoded = bincode_v1::deserialize::<NaiveTime>(&new_bytes)
            .expect("Bincode v1 should have been able to decode bytes encoded by Bincode v1.");
        assert_eq!(initial_value, decoded);
    }
}
