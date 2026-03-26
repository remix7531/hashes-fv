use hex_literal::hex;

#[cfg(feature = "sha256")]
mod sha256_tests {
    use super::*;

    #[test]
    fn empty() {
        assert_eq!(
            sha2::sha256(b""),
            hex!("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
        );
    }

    #[test]
    fn abc() {
        assert_eq!(
            sha2::sha256(b"abc"),
            hex!("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
        );
    }

    #[test]
    fn long_message() {
        assert_eq!(
            sha2::sha256(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
            hex!("248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")
        );
    }

    #[test]
    fn hello_world() {
        assert_eq!(
            sha2::sha256(b"hello world"),
            hex!("b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9")
        );
    }
}

#[cfg(feature = "sha256_224")]
mod sha224_tests {
    use super::*;

    #[test]
    fn empty() {
        assert_eq!(
            sha2::sha224(b""),
            hex!("d14a028c2a3a2bc9476102bb288234c415a2b01f828ea62ac5b3e42f")
        );
    }

    #[test]
    fn abc() {
        assert_eq!(
            sha2::sha224(b"abc"),
            hex!("23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7")
        );
    }

    #[test]
    fn long_message() {
        assert_eq!(
            sha2::sha224(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
            hex!("75388b16512776cc5dba5da1fd890150b0c6455cb4f58b1952522525")
        );
    }
}

#[cfg(feature = "sha512")]
mod sha512_tests {
    use super::*;

    #[test]
    fn empty() {
        assert_eq!(
            sha2::sha512(b""),
            hex!(
                "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce"
                "47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
            )
        );
    }

    #[test]
    fn abc() {
        assert_eq!(
            sha2::sha512(b"abc"),
            hex!(
                "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a"
                "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
            )
        );
    }

    #[test]
    fn long_message() {
        assert_eq!(
            sha2::sha512(b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"),
            hex!(
                "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018"
                "501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909"
            )
        );
    }

    #[test]
    fn hello_world() {
        assert_eq!(
            sha2::sha512(b"hello world"),
            hex!(
                "309ecc489c12d6eb4cc40f50c902f2b4d0ed77ee511a7c7a9bcd3ca86d4cd86f"
                "989dd35bc5ff499670da34255b45b0cfd830e81f605dcf7dc5542e93ae9cd76f"
            )
        );
    }
}

#[cfg(feature = "sha512_384")]
mod sha384_tests {
    use super::*;

    #[test]
    fn empty() {
        assert_eq!(
            sha2::sha384(b""),
            hex!(
                "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da"
                "274edebfe76f65fbd51ad2f14898b95b"
            )
        );
    }

    #[test]
    fn abc() {
        assert_eq!(
            sha2::sha384(b"abc"),
            hex!(
                "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed"
                "8086072ba1e7cc2358baeca134c825a7"
            )
        );
    }
}

#[cfg(feature = "sha512_224")]
mod sha512_224_tests {
    use super::*;

    #[test]
    fn empty() {
        assert_eq!(
            sha2::sha512_224(b""),
            hex!("6ed0dd02806fa89e25de060c19d3ac86cabb87d6a0ddd05c333b84f4")
        );
    }

    #[test]
    fn abc() {
        assert_eq!(
            sha2::sha512_224(b"abc"),
            hex!("4634270f707b6a54daae7530460842e20e37ed265ceee9a43e8924aa")
        );
    }
}

#[cfg(feature = "sha512_256")]
mod sha512_256_tests {
    use super::*;

    #[test]
    fn empty() {
        assert_eq!(
            sha2::sha512_256(b""),
            hex!("c672b8d1ef56ed28ab87c3622c5114069bdd3ad7b8f9737498d0c01ecef0967a")
        );
    }

    #[test]
    fn abc() {
        assert_eq!(
            sha2::sha512_256(b"abc"),
            hex!("53048e2681941ef99b2e29b76b4c7dabe4c2d0c634fc6d46e0e2f13107e7af23")
        );
    }
}
