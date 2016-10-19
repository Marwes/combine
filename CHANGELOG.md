<a name="2.0.0"></a>
## 2.0.0 (2016-10-19)


#### Features

*   Version 2.0.0 ([80b24186](https://github.com/Marwes/combine/commit/80b24186fb4854d3242f32abc727107545e08c7b))
*   Add the count parser ([a7949f3a](https://github.com/Marwes/combine/commit/a7949f3aef8585523e730e2c1224c3725b360d32))
*   Add the Parser::by_ref method ([15554d0c](https://github.com/Marwes/combine/commit/15554d0c64a2415e8c234708595cc544ada6c585))
*   Add the one_of and none_of parsers ([941b277c](https://github.com/Marwes/combine/commit/941b277c8f4d8e8af804c88678181be7743f912b))
*   Add the position parser ([d6c65f6d](https://github.com/Marwes/combine/commit/d6c65f6da5a2af47254abe2db4b04c3ecbd74803))
*   Add bytes_cmp and string_cmp ([ee6b430d](https://github.com/Marwes/combine/commit/ee6b430d17508daf305d5f48fabae2d662a94d34))
*   Add the `tokens` parser ([886c4523](https://github.com/Marwes/combine/commit/886c45235be207241874a0a412ebcc0733959466))
*   Version 2.0.0-beta3 ([55c59322](https://github.com/Marwes/combine/commit/55c59322f8ead037dad703a41e1f6d769c059f31))
*   Break out the error formatting into a separate function ([b6ccb0c1](https://github.com/Marwes/combine/commit/b6ccb0c1807f0f182878b68d4dbdcfa739fd5157))
*   Rename parse_state to parse_stream ([b375df48](https://github.com/Marwes/combine/commit/b375df4811570d14bbd8db7cb74a6834e54679cf))
*   Simplify the flat_map parser ([08a91ce2](https://github.com/Marwes/combine/commit/08a91ce201b67f5528a18228bdfb079e7d86dd7f))
*   Merge the ParserExt trait into Parser ([26a84154](https://github.com/Marwes/combine/commit/26a841540107b79542bb874a60abb83f99c78a58))
*   Add the bytes parser ([9c73c053](https://github.com/Marwes/combine/commit/9c73c053f37b149c35d60377f6dcbbbfc145dda9))
*   Add parsers specialized on byte streams ([01ba3759](https://github.com/Marwes/combine/commit/01ba375929daac2cb81a3e966e529f0909014620))
*   Make ctry usable outside the crate ([f45740dd](https://github.com/Marwes/combine/commit/f45740dd71cf9c71e0900e932c2f10ccbefae35e))
*   Add versions of parse_* which return an unpacked version of ParseResult ([2bbd14ab](https://github.com/Marwes/combine/commit/2bbd14abd2b372afbfda56fb73d4aa036bd427e1))
*   Add the satisy_map parser ([4d97d296](https://github.com/Marwes/combine/commit/4d97d2968c48026e8369e1f0bcee3c6ef5784664))
*   Replace the And parser with the pair parser ([b1f56113](https://github.com/Marwes/combine/commit/b1f561139169caa1a5a2e3e2d84248b28f22bb82))
*   Remove reexport of the char module from the root module ([e39dacb5](https://github.com/Marwes/combine/commit/e39dacb57999c3cfb0bb4ae6d5db0b696da60a3f))
*   Version 2.0.0-beta ([5bdbf584](https://github.com/Marwes/combine/commit/5bdbf58484800717c7d7c20b9161562520f425cb))
*   Remove the buffered_stream feature ([3fdbf217](https://github.com/Marwes/combine/commit/3fdbf217ec0a66b052b8d11792ce3ff3d13b7463))
*   Version 1.3.0 ([acea26cd](https://github.com/Marwes/combine/commit/acea26cda536ffc681ca4fa9e4c1bf28f5184582))
*   Add the eof parser ([6a89cbf2](https://github.com/Marwes/combine/commit/6a89cbf2ef11ed5bf4145a296c208e5f5f90438c))
*   Stabilize RangeStream and all functions using it ([d932375d](https://github.com/Marwes/combine/commit/d932375d13a196fc74602f8e76ad5bd3512ca370))
*   Reexport Stream and StreamOnce from the crate root ([2c2b3f5c](https://github.com/Marwes/combine/commit/2c2b3f5cd21a04fbc157a95ce76fe72bfdc1a2c3))
*   Merge the HasPosition trait into StreamOnce ([3bda4a16](https://github.com/Marwes/combine/commit/3bda4a163e8f3b57dd4efa65384c97f9c3554aeb))
*   Add the StreamOnce trait ([9ea0ed5d](https://github.com/Marwes/combine/commit/9ea0ed5d6c8f8cead773a24b968d4a0bbb606721), breaks [#](https://github.com/Marwes/combine/issues/))
*   Make Stream::uncons take &mut self ([4ddc4257](https://github.com/Marwes/combine/commit/4ddc4257d1e719a9f1c17a49c39f08ebf20d2999))
*   Separate the Position type and position method from Stream ([9cfb9a89](https://github.com/Marwes/combine/commit/9cfb9a895be34b288ee9fc9f926cd1b9c5b97b03))
*   Version 1.2.1 ([f737af27](https://github.com/Marwes/combine/commit/f737af27306160088188900a1cdad255b5ca58d3))
*   Move the position handling inside the Stream trait ([f41f65e9](https://github.com/Marwes/combine/commit/f41f65e9f34b64481f81af078ecdb10a80e75f6f))
* **range_stream:**  Implement RangeStream on State ([f5679dc9](https://github.com/Marwes/combine/commit/f5679dc954be093a7a0278d2311cf5a162396833))

#### Performance

*   Specialize and_then, then and flat_map ([9dc7dc6b](https://github.com/Marwes/combine/commit/9dc7dc6b9bcb638888be448efb7002d362aded16))
*   Specialize the tuple parser to avoid unnecessary branches ([2b294f80](https://github.com/Marwes/combine/commit/2b294f8009021897d9652981dfb107dd2102a902))
*   Add inline annotations and more forwarding parse functions ([0e5ee38e](https://github.com/Marwes/combine/commit/0e5ee38e1b15847908f6676c0c4032dc844e3462))
*   Avoid indirection in Skip and With ([52d335ca](https://github.com/Marwes/combine/commit/52d335caa2e698de9be50e46e8fbcf241d4e3081))
*   Optimize Iter by simplifying the state machine ([9631700a](https://github.com/Marwes/combine/commit/9631700a306cb5546e37dfb8f05d54728fb3bc8c))
*   Speedup tuple parsers by simplifying the expanded code ([5d86dcf2](https://github.com/Marwes/combine/commit/5d86dcf2d14f1cae078d1a4b8831d37041eaf7a2))
*   Avoid creating an error when take_while1 parses no input ([9bad15c0](https://github.com/Marwes/combine/commit/9bad15c0f79e3ff897fb92cdca6b92f988c69347))
*   Possibly improve performance of the RangeStream impl for &str ([abb1de7f](https://github.com/Marwes/combine/commit/abb1de7f15b65b9bc2c40572319269191bd0819f))

#### Bug Fixes

*   Rename the String parser to Str ([d846bf0e](https://github.com/Marwes/combine/commit/d846bf0e7ddb3350ce9245b3682d7c054ff5cdd8))
*   Use five copies in the large http test anyway to match nom_benchmarks ([eb089f5b](https://github.com/Marwes/combine/commit/eb089f5bef175b96e097286b9c8c3e7d5f6e3922))
*   Avoid storing the position in primitives::uncons_while ([9912507a](https://github.com/Marwes/combine/commit/9912507a80e178737e16d4ff3d19d7a1fee9fbc8))
*   Calling uncons_range with the same size as is remaining should succeed ([cce6214e](https://github.com/Marwes/combine/commit/cce6214ed4722880881c8c6998e00f4509a22588))
*   Add Sync to to the Error::Other variant ([22add3ec](https://github.com/Marwes/combine/commit/22add3eca62ff5e6f4d58122a4b366290b1d9385))
*   Fix positions of BufferedStream being for the next token ([66eab92a](https://github.com/Marwes/combine/commit/66eab92a7dd63269f48cf0fbd0722a6eeea9135d))
*   Fix the position handling of BufferedStream ([f21148b3](https://github.com/Marwes/combine/commit/f21148b3c4c5c6f10d8b6d90ce4a7925596879b3))
*   Remove the Positioner bound from Stream::Item an Stream::Range ([fba3f1e7](https://github.com/Marwes/combine/commit/fba3f1e760505305b6a586b6ff5a53eff645e1d1))
* **buffered_stream:**  BufferedStream no longer emits the last token after EOF ([6532884c](https://github.com/Marwes/combine/commit/6532884cc16307e1753584dd40b2b59e3daa6267))
* **travis:**
  *  Dont pass the test feature to travis ([382a608d](https://github.com/Marwes/combine/commit/382a608da2851c5cc2d3477025951e9a133732bc))
  *  Add travis_wait so travis does not time out the beta builds ([a3f0792a](https://github.com/Marwes/combine/commit/a3f0792ab347805e3f0ce619997a2c154f5e8c87))

#### Breaking Changes

*   Add the StreamOnce trait ([9ea0ed5d](https://github.com/Marwes/combine/commit/9ea0ed5d6c8f8cead773a24b968d4a0bbb606721), breaks [#](https://github.com/Marwes/combine/issues/))
