#![cfg(feature = "mp4")]
#![feature(test)]
extern crate test;

extern crate combine;
extern crate byteorder;

use test::{Bencher, black_box};

use std::str::from_utf8;

use byteorder::{BigEndian, ByteOrder};

use combine::*;
use combine::range::{range, take};

#[derive(Clone, PartialEq, Eq, Debug)]
struct FileType<'a> {
    major_brand: &'a str,
    major_brand_version: &'a [u8],
    compatible_brands: Vec<&'a str>,
}

#[derive(Clone, Debug)]
enum MP4Box<'a> {
    Ftyp(FileType<'a>),
    Moov,
    Mdat,
    Free,
    Skip,
    Wide,
    Unknown,
}

fn parse_mp4(data: &[u8]) -> Result<(Vec<MP4Box>, &[u8]), ParseError<&[u8]>> {
    let brand_name = || take(4).and_then(from_utf8);
    let filetype_box = (range(&b"ftyp"[..]), brand_name(), take(4), many(brand_name()))
        .map(|(_, m, v, c)| {
            MP4Box::Ftyp(FileType {
                             major_brand: m,
                             major_brand_version: v,
                             compatible_brands: c,
                         })
        });

    let mp4_box = take(4).map(BigEndian::read_u32).then(|offset| take(offset as usize - 4));
    let mut box_parser = filetype_box.or(range(&b"moov"[..]).map(|_| MP4Box::Moov))
        .or(range(&b"mdat"[..]).map(|_| MP4Box::Mdat))
        .or(range(&b"free"[..]).map(|_| MP4Box::Free))
        .or(range(&b"skip"[..]).map(|_| MP4Box::Skip))
        .or(range(&b"wide"[..]).map(|_| MP4Box::Wide))
        .or(value(MP4Box::Unknown));
    let data_interpreter = mp4_box.flat_map(|box_data| box_parser.parse(box_data).map(|t| t.0));

    many(data_interpreter).parse(data)
}

static MP4_SMALL: &'static [u8] = include_bytes!("small.mp4");

fn run_test(b: &mut Bencher, data: &[u8]) {
    b.iter(|| match parse_mp4(data) {
               Ok(x) => black_box(x),
               Err(err) => panic!("{:?}", err),
           });
}

#[bench]
fn mp4_small_test(b: &mut Bencher) {
    run_test(b, MP4_SMALL)
}
