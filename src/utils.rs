use rtlola_frontend::ir::StreamReference::OutRef;
use rtlola_frontend::ir::{MemorizationBound, StreamReference};
use rtlola_frontend::RTLolaIR;
use std::collections::{btree_map, hash_map, BTreeMap, HashMap, HashSet};

/// calculate the maximum memory bound (max_mem) of the RTLola specification
/// * `ir` - RTLolaIR from which the streams come
pub fn max_memory_bound(ir: &RTLolaIR) -> u16 {
  let mut max_mem = 1;
  for i in &ir.all_streams() {
    let mem;
    match i {
      StreamReference::InRef(_) => {
        if let MemorizationBound::Bounded(v) = ir.get_in(*i).memory_bound {
          mem = v;
        } else {
          panic!("max memory bound: memorization bound is not allowed to be unbounded!");
        }
      }
      OutRef(_) => {
        if let MemorizationBound::Bounded(v) = ir.get_out(*i).memory_bound {
          mem = v;
        } else {
          panic!("max memory bound: memorization bound is not allowed to be unbounded!");
        }
      }
    }
    if max_mem < mem {
      max_mem = mem;
    }
  }
  max_mem - 1
}

/// return map which maps every stream onto the streams which access this stream
/// * `ir` - RTLolaIR from which the streams come
fn get_dependent_streams(ir: &RTLolaIR) -> (HashMap<&StreamReference, Vec<&StreamReference>>, Vec<&StreamReference>) {
  let mut dependent_streams: HashMap<&StreamReference, Vec<&StreamReference>> = HashMap::new();
  let mut recursive_streams: Vec<&StreamReference> = Vec::new();
  for stream in &ir.outputs {
    for dep in &stream.outgoing_dependencies {
      if dep.stream == stream.reference {
        if !recursive_streams.contains(&&stream.reference) {
          recursive_streams.push(&stream.reference);
        }
      } else {
        if let StreamReference::OutRef(_) = &dep.stream {
          match dependent_streams.entry(&dep.stream) {
            hash_map::Entry::Vacant(e) => {
              e.insert(vec![&stream.reference]);
            }
            hash_map::Entry::Occupied(mut e) => {
              e.get_mut().push(&stream.reference);
            }
          }
        }
      }
    }
  }
  (dependent_streams, recursive_streams)
}

/// return map which maps every stream onto the streams which it accesses
/// * `ir` - RTLolaIR from which the streams come
pub fn get_accessed_streams(ir: &RTLolaIR) -> HashMap<&StreamReference, Vec<&StreamReference>> {
  let mut accessed_streams_map: HashMap<&StreamReference, Vec<&StreamReference>> = HashMap::new();
  let mut changed;
  for stream in &ir.outputs {
    let mut accessed = HashSet::new();
    for dep in &stream.outgoing_dependencies {
      if dep.stream != stream.reference {
        if let StreamReference::OutRef(_) = &dep.stream {
          match accessed_streams_map.entry(&stream.reference) {
            hash_map::Entry::Vacant(e) => {
              e.insert(vec![&dep.stream]);
            }
            hash_map::Entry::Occupied(mut e) => {
              e.get_mut().push(&dep.stream);
            }
          }
          // println!("{}: {} depends on {}", stream.name, stream.name, ir.get_out(dep.stream).name);
          accessed.insert(&dep.stream);
        }
      }
    }
    changed = !accessed.is_empty();
    while changed {
      let mut new_accessed = HashSet::new();
      for already_accessed in &accessed {
        for dep in &ir.get_out(**already_accessed).outgoing_dependencies {
          let known = accessed_streams_map.get(&stream.reference);
          if known.is_some() && !known.unwrap().contains(&&dep.stream) {
            if let StreamReference::OutRef(_) = &dep.stream {
              match accessed_streams_map.entry(&stream.reference) {
                hash_map::Entry::Vacant(e) => {
                  e.insert(vec![&dep.stream]);
                }
                hash_map::Entry::Occupied(mut e) => {
                  e.get_mut().push(&dep.stream);
                }
              }
              new_accessed.insert(&dep.stream);
            }
          }
        }
      }
      if new_accessed.is_empty() {
        changed = false;
      } else {
        changed = true;
        accessed = new_accessed;
      }
    }
  }
  accessed_streams_map
}

/// map different layers onto the streams which are executed in this layer
/// * `streams` - vector of streams which should be sorted
/// * `ir` - RTLolaIR from which the streams come
fn get_layer_map<'a>(streams: &Vec<&'a StreamReference>, ir: &RTLolaIR) -> BTreeMap<u32, Vec<&'a StreamReference>> {
  // use BTreeMap as BTreeMap is like sorted HashMap (increasing order)
  let mut map = BTreeMap::new();
  for v in streams {
    let stream = ir.get_out(**v);
    let mem = stream.layer;
    match map.entry(mem) {
      btree_map::Entry::Vacant(e) => {
        e.insert(vec![*v]);
      }
      btree_map::Entry::Occupied(mut e) => {
        e.get_mut().push(*v);
      }
    }
  }
  map
}

/// sort streams per evaluation layer and return sorted vector
/// * `streams` - vector of streams which should be sorted
/// * `len` - highest possible evaluation layer (number of streams is always an upperbound)
/// * `ir` - RTLolaIR from which the streams come
pub fn sort_per_layer<'a>(streams: &Vec<&'a StreamReference>, len: usize, ir: &RTLolaIR) -> Vec<&'a StreamReference> {
  let layer_map = get_layer_map(streams, ir);
  let mut res = Vec::new();
  for (_, val) in layer_map {
    for j in 0..len {
      for v in &val {
        if let OutRef(num) = v {
          if j == *num {
            res.push(*v);
            break;
          }
        }
      }
    }
  }
  res
}

/// split streams in linear and recursive streams and return respective vectors
/// * `ir` - RTLolaIR from which the streams come
pub fn get_linear_and_recursive_streams(ir: &RTLolaIR) -> (Vec<&StreamReference>, Vec<&StreamReference>) {
  let mut linear_streams = Vec::new();
  let (dependent_streams, mut recursive_streams) = get_dependent_streams(ir);
  let map_accessed = get_accessed_streams(ir);

  for (current_stream, accessed_streams) in &map_accessed {
    for accessed_stream_ref in accessed_streams {
      let accesed_streams_by_access = map_accessed.get(accessed_stream_ref);
      if accesed_streams_by_access.is_some() {
        for accessed_by_access in accesed_streams_by_access.unwrap() {
          if *accessed_by_access == *current_stream {
            if !recursive_streams.contains(current_stream) {
              recursive_streams.push(*current_stream);
            }
          }
        }
      }
    }
  }
  for stream in &ir.outputs {
    let stream_ref = &stream.reference;
    if recursive_streams.contains(&stream_ref) {
      let deps = dependent_streams.get(stream_ref);
      if deps.is_some() {
        for r in deps.unwrap() {
          if !recursive_streams.contains(r) {
            recursive_streams.push(*r);
          }
        }
      }
    }
  }
  for stream in &ir.outputs {
    if recursive_streams.contains(&&stream.reference) {
      println!("Attention: {} is recursive and can not be analyzed symbolically!", stream.name);
    } else {
      linear_streams.push(&stream.reference);
    }
  }
  (linear_streams, recursive_streams)
}
