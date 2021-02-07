use tinyvec::TinyVec;
use std::{
    cmp,
    cmp::Ordering,
    collections::{
        btree_map, BTreeMap,
        Bound::{Excluded, Included},
        VecDeque,
    },
    ops::Range,
};

// /// A set of u64 values optimized for long runs and random insert/delete/contains
// #[derive(Debug, Default, Clone)]
// pub struct CompactRangeSet(VecDeque<Range<u64>>);

// pub struct CompactRangeSetIter<'a> {
//     inner: &'a VecDeque<Range<u64>>,
//     front_idx: usize,
//     back_idx: usize,
// }

// impl<'a> Iterator for CompactRangeSetIter<'a> {
//     type Item = Range<u64>;

//     fn next(&mut self) -> Option<Self::Item> {
//         if self.front_idx == self.back_idx {
//             None
//         } else {
//             let elem = self.inner.get(self.front_idx).cloned();
//             self.front_idx += 1;
//             elem
//         }
//     }
// }

// impl<'a> DoubleEndedIterator for CompactRangeSetIter<'a> {
//     fn next_back(&mut self) -> Option<Self::Item> {
//         if self.back_idx == self.front_idx {
//             None
//         } else {
//             self.back_idx -= 1;
//             self.inner.get(self.back_idx).cloned()
//         }
//     }
// }

// pub struct CompactEltIter<'a> {
//     inner: CompactRangeSetIter<'a>,
//     start: u64,
//     end: u64,
// }

// impl<'a> Iterator for CompactEltIter<'a> {
//     type Item = u64;
//     fn next(&mut self) -> Option<u64> {
//         if self.start == self.end {
//             let next_range = self.inner.next()?;
//             self.start = next_range.start;
//             self.end = next_range.end;
//         }
//         let x = self.start;
//         self.start += 1;
//         Some(x)
//     }
// }

// fn intersect(a: Range<u64>, b: Range<u64>) -> Range<u64> {
//     if a.start > b.end || b.start > a.end {
//         return 0..0;
//     }

//     let start = a.start.max(b.start);
//     let end = a.end.min(b.end);

//     if start > end {
//         0 .. 0
//     } else {
//         start .. end
//     }
// }

// impl CompactRangeSet {
//     pub fn new() -> Self {
//         Default::default()
//     }

//     pub fn iter(&self) -> CompactRangeSetIter<'_> {
//         CompactRangeSetIter {
//             inner: &self.0,
//             front_idx: 0,
//             back_idx: self.0.len(),
//         }
//     }

//     pub fn elts(&self) -> CompactEltIter<'_> {
//         CompactEltIter {
//             inner: self.iter(),
//             start: 0,
//             end: 0,
//         }
//     }

//     pub fn len(&self) -> usize {
//         self.0.len()
//     }

//     pub fn contains(&self, x: u64) -> bool {
//         self.0.iter().any(|range|range.contains(&x))
//     }

//     pub fn subtract(&mut self, other: &CompactRangeSet) {
//         for range in &other.0 {
//             self.remove(range.clone());
//         }
//     }

//     pub fn insert_one(&mut self, x: u64) -> bool {
//         let mut idx = 0;
//         while idx != self.0.len() {
//             let range = &mut self.0[idx];

//             if x + 1 == range.start {
//                 // Extend the range to the left
//                 // Note that we don't have to merge the left range, since
//                 // this case would have been captured by merging the right range
//                 // in the previous loop iteration
//                 range.start = x;
//                 return true;
//             } else if x < range.start {
//                 // Not extensible. Add a new range to the left
//                 self.0.insert(idx, x .. x + 1);
//                 return true;
//             } else if x >= range.start && x < range.end {
//                 // Fully contained
//                 return false;
//             } else if x == range.end {
//                 // Extend the range to the end
//                 range.end += 1;

//                 // Merge the next range
//                 if idx != self.0.len() - 1 {
//                     let curr = self.0[idx].clone();
//                     let next = self.0[idx + 1].clone();
//                     if curr.end == next.start {
//                         self.0[idx].end = next.end;
//                         self.0.remove(idx + 1);
//                     }
//                 }

//                 return true;
//             }

//             idx += 1;
//         }

//         self.0.push_back(x .. x + 1);
//         true
//     }

//     #[cfg(test)]
//     pub fn insert(&mut self, x: Range<u64>) -> bool {
//         let mut result = false;
//         for v in x {
//             result |= self.insert_one(v);
//         }

//         assert!(self.0.len() < 100);

//         result
//     }

//     pub fn remove(&mut self, mut x: Range<u64>) -> bool {
//         let mut result = false;

//         let mut idx = 0;
//         while idx != self.0.len() && x.start != x.end {
//             let range = self.0[idx].clone();

//             if x.end <= range.start {
//                 // The range is fully before this range
//                 return result;
//             } else if x.start >= range.end {
//                 // The range is fully after this range
//                 idx += 1;
//             } else {
//                 // The range overlaps with this range
//                 result = true;

//                 // Trim everything off the range which is in front of this range
//                 x.start = x.start.max(range.start);

//                 // This is what we remove from this particular range
//                 let to_remove = x.start .. x.end.min(range.end);

//                 // Everything which is after thing range will be handled in the
//                 // next loop iteration
//                 x.start = range.end.min(x.end);

//                 debug_assert!(range.start <= to_remove.start);
//                 debug_assert!(to_remove.end <= range.end);

//                 let left = range.start .. to_remove.start;
//                 let right = to_remove.end .. range.end;

//                 let left_len = left.end - left.start;
//                 let right_len= right.end - right.start;

//                 debug_assert!(left_len + right_len <= range.end - range.start);

//                 if left_len == 0 && right_len == 0 {
//                     // We drained the range
//                     self.0.remove(idx);
//                 } else if left_len != 0 && right_len != 0 {
//                     self.0[idx] = right;
//                     self.0.insert(idx, left);
//                     idx += 2;
//                 } else if left_len != 0 {
//                     self.0[idx] = left;
//                     idx += 1;
//                 } else {
//                     self.0[idx] = right;
//                     idx += 1;
//                 }
//             }
//         }

//         result
//     }

//     pub fn is_empty(&self) -> bool {
//         self.0.is_empty()
//     }

//     pub fn pop_min(&mut self) -> Option<Range<u64>> {
//         self.0.pop_front()
//     }
// }

#[derive(Default, Clone, Copy, PartialEq, Eq)]
struct MyRange {
    start: u64,
    end: u64,
}

impl Into<Range<u64>> for MyRange {
    fn into(self) -> Range<u64> {
        Range {
            start: self.start,
            end: self.end,
        }
    }
}

impl From<Range<u64>> for MyRange {
    fn from(r: Range<u64>) -> Self {
        Self {
            start: r.start,
            end: r.end,
        }
    }
}

/// A set of u64 values optimized for long runs and random insert/delete/contains
#[derive(Debug, Clone, Default)]
pub struct CompactRangeSet(TinyVec<[Range<u64>; 2]>);

pub struct CompactRangeSetIter<'a> {
    inner: &'a TinyVec<[Range<u64>; 2]>,
    front_idx: usize,
    back_idx: usize,
}

impl<'a> Iterator for CompactRangeSetIter<'a> {
    type Item = Range<u64>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.front_idx == self.back_idx {
            None
        } else {
            let elem = self.inner.get(self.front_idx).cloned();
            self.front_idx += 1;
            elem
        }
    }
}

impl<'a> DoubleEndedIterator for CompactRangeSetIter<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.back_idx == self.front_idx {
            None
        } else {
            self.back_idx -= 1;
            self.inner.get(self.back_idx).cloned()
        }
    }
}

pub struct CompactEltIter<'a> {
    inner: CompactRangeSetIter<'a>,
    start: u64,
    end: u64,
}

impl<'a> Iterator for CompactEltIter<'a> {
    type Item = u64;
    fn next(&mut self) -> Option<u64> {
        if self.start == self.end {
            let next_range = self.inner.next()?;
            self.start = next_range.start;
            self.end = next_range.end;
        }
        let x = self.start;
        self.start += 1;
        Some(x)
    }
}

fn intersect(a: Range<u64>, b: Range<u64>) -> Range<u64> {
    if a.start > b.end || b.start > a.end {
        return 0..0;
    }

    let start = a.start.max(b.start);
    let end = a.end.min(b.end);

    if start > end {
        0..0
    } else {
        start..end
    }
}

impl CompactRangeSet {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn iter(&self) -> CompactRangeSetIter<'_> {
        CompactRangeSetIter {
            inner: &self.0,
            front_idx: 0,
            back_idx: self.0.len(),
        }
    }

    pub fn elts(&self) -> CompactEltIter<'_> {
        CompactEltIter {
            inner: self.iter(),
            start: 0,
            end: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn contains(&self, x: u64) -> bool {
        self.0.iter().any(|range| range.contains(&x))
    }

    pub fn subtract(&mut self, other: &CompactRangeSet) {
        for range in &other.0 {
            self.remove(range.clone());
        }
    }

    pub fn insert_one(&mut self, x: u64) -> bool {
        let mut idx = 0;
        while idx != self.0.len() {
            let range = &mut self.0[idx];

            if x + 1 == range.start {
                // Extend the range to the left
                // Note that we don't have to merge the left range, since
                // this case would have been captured by merging the right range
                // in the previous loop iteration
                range.start = x;
                return true;
            } else if x < range.start {
                // Not extensible. Add a new range to the left
                self.0.insert(idx, x..x + 1);
                return true;
            } else if x >= range.start && x < range.end {
                // Fully contained
                return false;
            } else if x == range.end {
                // Extend the range to the end
                range.end += 1;

                // Merge the next range
                if idx != self.0.len() - 1 {
                    let curr = self.0[idx].clone();
                    let next = self.0[idx + 1].clone();
                    if curr.end == next.start {
                        self.0[idx].end = next.end;
                        self.0.remove(idx + 1);
                    }
                }

                return true;
            }

            idx += 1;
        }

        self.0.push(x..x + 1);
        true
    }

    #[cfg(test)]
    pub fn insert(&mut self, x: Range<u64>) -> bool {
        let mut result = false;
        for v in x {
            result |= self.insert_one(v);
        }

        assert!(self.0.len() < 100);

        result
    }

    pub fn remove(&mut self, mut x: Range<u64>) -> bool {
        let mut result = false;

        let mut idx = 0;
        while idx != self.0.len() && x.start != x.end {
            let range = self.0[idx].clone();

            if x.end <= range.start {
                // The range is fully before this range
                return result;
            } else if x.start >= range.end {
                // The range is fully after this range
                idx += 1;
            } else {
                // The range overlaps with this range
                result = true;

                // Trim everything off the range which is in front of this range
                x.start = x.start.max(range.start);

                // This is what we remove from this particular range
                let to_remove = x.start..x.end.min(range.end);

                // Everything which is after thing range will be handled in the
                // next loop iteration
                x.start = range.end.min(x.end);

                debug_assert!(range.start <= to_remove.start);
                debug_assert!(to_remove.end <= range.end);

                let left = range.start..to_remove.start;
                let right = to_remove.end..range.end;

                let left_len = left.end - left.start;
                let right_len = right.end - right.start;

                debug_assert!(left_len + right_len <= range.end - range.start);

                if left_len == 0 && right_len == 0 {
                    // We drained the range
                    self.0.remove(idx);
                } else if left_len != 0 && right_len != 0 {
                    self.0[idx] = right;
                    self.0.insert(idx, left);
                    idx += 2;
                } else if left_len != 0 {
                    self.0[idx] = left;
                    idx += 1;
                } else {
                    self.0[idx] = right;
                    idx += 1;
                }
            }
        }

        result
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn pop_min(&mut self) -> Option<Range<u64>> {
        if self.0.len() > 0 {
            Some(self.0.remove(0))
        } else {
            None
        }
    }
}

/// A set of u64 values optimized for long runs and random insert/delete/contains
#[derive(Debug, Default, Clone)]
pub struct RangeSet(BTreeMap<u64, u64>);

impl RangeSet {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn contains(&self, x: u64) -> bool {
        self.pred(x).map_or(false, |(_, end)| end > x)
    }

    pub fn insert_one(&mut self, x: u64) -> bool {
        if let Some((start, end)) = self.pred(x) {
            match end.cmp(&x) {
                // Wholly contained
                Ordering::Greater => {
                    return false;
                }
                Ordering::Equal => {
                    // Extend existing
                    self.0.remove(&start);
                    let mut new_end = x + 1;
                    if let Some((next_start, next_end)) = self.succ(x) {
                        if next_start == new_end {
                            self.0.remove(&next_start);
                            new_end = next_end;
                        }
                    }
                    self.0.insert(start, new_end);
                    return true;
                }
                _ => {}
            }
        }
        let mut new_end = x + 1;
        if let Some((next_start, next_end)) = self.succ(x) {
            if next_start == new_end {
                self.0.remove(&next_start);
                new_end = next_end;
            }
        }
        self.0.insert(x, new_end);
        true
    }

    pub fn insert(&mut self, mut x: Range<u64>) -> bool {
        if x.end == 0 || x.start == x.end {
            return false;
        }
        if let Some((start, end)) = self.pred(x.start) {
            if end >= x.end {
                // Wholly contained
                return false;
            } else if end >= x.start {
                // Extend overlapping predecessor
                self.0.remove(&start);
                x.start = start;
            }
        }
        while let Some((next_start, next_end)) = self.succ(x.start) {
            if next_start > x.end {
                break;
            }
            // Overlaps with successor
            self.0.remove(&next_start);
            x.end = cmp::max(next_end, x.end);
        }
        self.0.insert(x.start, x.end);
        true
    }

    /// Find closest range to `x` that begins at or before it
    fn pred(&self, x: u64) -> Option<(u64, u64)> {
        self.0
            .range((Included(0), Included(x)))
            .rev()
            .next()
            .map(|(&x, &y)| (x, y))
    }

    /// Find the closest range to `x` that begins after it
    fn succ(&self, x: u64) -> Option<(u64, u64)> {
        self.0
            .range((Excluded(x), Included(u64::max_value())))
            .next()
            .map(|(&x, &y)| (x, y))
    }

    pub fn remove(&mut self, x: Range<u64>) -> bool {
        let before = match self.pred(x.start) {
            Some((start, end)) if end > x.start => {
                self.0.remove(&start);
                if start < x.start {
                    self.0.insert(start, x.start);
                }
                if end > x.end {
                    self.0.insert(x.end, end);
                }
                // Short-circuit if we cannot possibly overlap with another range
                if end >= x.end {
                    return true;
                }
                true
            }
            Some(_) | None => false,
        };
        let mut after = false;
        while let Some((start, end)) = self.succ(x.start) {
            if start >= x.end {
                break;
            }
            after = true;
            self.0.remove(&start);
            if end > x.end {
                self.0.insert(x.end, end);
                break;
            }
        }
        before || after
    }

    /// Add a range to the set, returning the intersection of current ranges with the new one
    pub fn replace(&mut self, mut range: Range<u64>) -> Replace<'_> {
        let pred = if let Some((prev_start, prev_end)) = self
            .pred(range.start)
            .filter(|&(_, end)| end >= range.start)
        {
            self.0.remove(&prev_start);
            let replaced_start = range.start;
            range.start = range.start.min(prev_start);
            let replaced_end = range.end.min(prev_end);
            range.end = range.end.max(prev_end);
            if replaced_start != replaced_end {
                Some(replaced_start..replaced_end)
            } else {
                None
            }
        } else {
            None
        };
        Replace {
            set: self,
            range,
            pred,
        }
    }

    pub fn add(&mut self, other: &RangeSet) {
        for (&start, &end) in &other.0 {
            self.insert(start..end);
        }
    }

    pub fn subtract(&mut self, other: &RangeSet) {
        for (&start, &end) in &other.0 {
            self.remove(start..end);
        }
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn min(&self) -> Option<u64> {
        self.iter().next().map(|x| x.start)
    }
    pub fn max(&self) -> Option<u64> {
        self.iter().rev().next().map(|x| x.end - 1)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn iter(&self) -> Iter<'_> {
        Iter(self.0.iter())
    }
    pub fn elts(&self) -> EltIter<'_> {
        EltIter {
            inner: self.0.iter(),
            next: 0,
            end: 0,
        }
    }

    pub fn peek_min(&self) -> Option<Range<u64>> {
        let (&start, &end) = self.0.iter().next()?;
        Some(start..end)
    }

    pub fn pop_min(&mut self) -> Option<Range<u64>> {
        let result = self.peek_min()?;
        self.0.remove(&result.start);
        Some(result)
    }
}

pub struct Iter<'a>(btree_map::Iter<'a, u64, u64>);

impl<'a> Iterator for Iter<'a> {
    type Item = Range<u64>;
    fn next(&mut self) -> Option<Range<u64>> {
        let (&start, &end) = self.0.next()?;
        Some(start..end)
    }
}

impl<'a> DoubleEndedIterator for Iter<'a> {
    fn next_back(&mut self) -> Option<Range<u64>> {
        let (&start, &end) = self.0.next_back()?;
        Some(start..end)
    }
}

impl<'a> IntoIterator for &'a RangeSet {
    type Item = Range<u64>;
    type IntoIter = Iter<'a>;
    fn into_iter(self) -> Iter<'a> {
        self.iter()
    }
}

pub struct EltIter<'a> {
    inner: btree_map::Iter<'a, u64, u64>,
    next: u64,
    end: u64,
}

impl<'a> Iterator for EltIter<'a> {
    type Item = u64;
    fn next(&mut self) -> Option<u64> {
        if self.next == self.end {
            let (&start, &end) = self.inner.next()?;
            self.next = start;
            self.end = end;
        }
        let x = self.next;
        self.next += 1;
        Some(x)
    }
}

impl<'a> DoubleEndedIterator for EltIter<'a> {
    fn next_back(&mut self) -> Option<u64> {
        if self.next == self.end {
            let (&start, &end) = self.inner.next_back()?;
            self.next = start;
            self.end = end;
        }
        self.end -= 1;
        Some(self.end)
    }
}

/// Iterator returned by `RangeSet::replace`
pub struct Replace<'a> {
    set: &'a mut RangeSet,
    /// Portion of the intersection arising from a range beginning at or before the newly inserted
    /// range
    pred: Option<Range<u64>>,
    /// Union of the input range and all ranges that have been visited by the iterator so far
    range: Range<u64>,
}

impl Iterator for Replace<'_> {
    type Item = Range<u64>;
    fn next(&mut self) -> Option<Range<u64>> {
        if let Some(pred) = self.pred.take() {
            // If a range starting before the inserted range overlapped with it, return the
            // corresponding overlap first
            return Some(pred);
        }

        let (next_start, next_end) = self.set.succ(self.range.start)?;
        if next_start > self.range.end {
            // If the next successor range starts after the current range ends, there can be no more
            // overlaps. This is sound even when `self.range.end` is increased because `RangeSet` is
            // guaranteed not to contain pairs of ranges that could be simplified.
            return None;
        }
        // Remove the redundant range...
        self.set.0.remove(&next_start);
        // ...and handle the case where the redundant range ends later than the new range.
        let replaced_end = self.range.end.min(next_end);
        self.range.end = self.range.end.max(next_end);
        if next_start == replaced_end {
            // If the redundant range started exactly where the new range ended, there was no
            // overlap with it or any later range.
            None
        } else {
            Some(next_start..replaced_end)
        }
    }
}

impl Drop for Replace<'_> {
    fn drop(&mut self) {
        // Ensure we drain all remaining overlapping ranges
        while let Some(_) = self.next() {}
        // Insert the final aggregate range
        self.set.0.insert(self.range.start, self.range.end);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn merge_and_split() {
        let mut set = RangeSet::new();
        assert!(set.insert(0..2));
        assert!(set.insert(2..4));
        assert!(!set.insert(1..3));
        assert_eq!(set.len(), 1);
        assert_eq!(&set.elts().collect::<Vec<_>>()[..], [0, 1, 2, 3]);
        assert!(!set.contains(4));
        assert!(set.remove(2..3));
        assert_eq!(set.len(), 2);
        assert!(!set.contains(2));
        assert_eq!(&set.elts().collect::<Vec<_>>()[..], [0, 1, 3]);
    }

    #[test]
    fn double_merge_exact() {
        let mut set = RangeSet::new();
        assert!(set.insert(0..2));
        assert!(set.insert(4..6));
        assert_eq!(set.len(), 2);
        assert!(set.insert(2..4));
        assert_eq!(set.len(), 1);
        assert_eq!(&set.elts().collect::<Vec<_>>()[..], [0, 1, 2, 3, 4, 5]);
    }

    #[test]
    fn single_merge_low() {
        let mut set = RangeSet::new();
        assert!(set.insert(0..2));
        assert!(set.insert(4..6));
        assert_eq!(set.len(), 2);
        assert!(set.insert(2..3));
        assert_eq!(set.len(), 2);
        assert_eq!(&set.elts().collect::<Vec<_>>()[..], [0, 1, 2, 4, 5]);
    }

    #[test]
    fn single_merge_high() {
        let mut set = RangeSet::new();
        assert!(set.insert(0..2));
        assert!(set.insert(4..6));
        assert_eq!(set.len(), 2);
        assert!(set.insert(3..4));
        assert_eq!(set.len(), 2);
        assert_eq!(&set.elts().collect::<Vec<_>>()[..], [0, 1, 3, 4, 5]);
    }

    #[test]
    fn double_merge_wide() {
        let mut set = RangeSet::new();
        assert!(set.insert(0..2));
        assert!(set.insert(4..6));
        assert_eq!(set.len(), 2);
        assert!(set.insert(1..5));
        assert_eq!(set.len(), 1);
        assert_eq!(&set.elts().collect::<Vec<_>>()[..], [0, 1, 2, 3, 4, 5]);
    }

    #[test]
    fn double_remove() {
        let mut set = RangeSet::new();
        assert!(set.insert(0..2));
        assert!(set.insert(4..6));
        assert!(set.remove(1..5));
        assert_eq!(set.len(), 2);
        assert_eq!(&set.elts().collect::<Vec<_>>()[..], [0, 5]);
    }

    #[test]
    fn insert_multiple() {
        let mut set = RangeSet::new();
        assert!(set.insert(0..1));
        assert!(set.insert(2..3));
        assert!(set.insert(4..5));
        assert!(set.insert(0..5));
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn remove_multiple() {
        let mut set = RangeSet::new();
        assert!(set.insert(0..1));
        assert!(set.insert(2..3));
        assert!(set.insert(4..5));
        assert!(set.remove(0..5));
        assert!(set.is_empty());
    }

    #[test]
    fn replace_contained() {
        let mut set = RangeSet::new();
        set.insert(2..4);
        assert_eq!(set.replace(1..5).collect::<Vec<_>>(), &[2..4]);
        assert_eq!(set.len(), 1);
        assert_eq!(set.peek_min().unwrap(), 1..5);
    }

    #[test]
    fn replace_contains() {
        let mut set = RangeSet::new();
        set.insert(1..5);
        assert_eq!(set.replace(2..4).collect::<Vec<_>>(), &[2..4]);
        assert_eq!(set.len(), 1);
        assert_eq!(set.peek_min().unwrap(), 1..5);
    }

    #[test]
    fn replace_pred() {
        let mut set = RangeSet::new();
        set.insert(2..4);
        assert_eq!(set.replace(3..5).collect::<Vec<_>>(), &[3..4]);
        assert_eq!(set.len(), 1);
        assert_eq!(set.peek_min().unwrap(), 2..5);
    }

    #[test]
    fn replace_succ() {
        let mut set = RangeSet::new();
        set.insert(2..4);
        assert_eq!(set.replace(1..3).collect::<Vec<_>>(), &[2..3]);
        assert_eq!(set.len(), 1);
        assert_eq!(set.peek_min().unwrap(), 1..4);
    }

    #[test]
    fn replace_exact_pred() {
        let mut set = RangeSet::new();
        set.insert(2..4);
        assert_eq!(set.replace(4..6).collect::<Vec<_>>(), &[]);
        assert_eq!(set.len(), 1);
        assert_eq!(set.peek_min().unwrap(), 2..6);
    }

    #[test]
    fn replace_exact_succ() {
        let mut set = RangeSet::new();
        set.insert(2..4);
        assert_eq!(set.replace(0..2).collect::<Vec<_>>(), &[]);
        assert_eq!(set.len(), 1);
        assert_eq!(set.peek_min().unwrap(), 0..4);
    }

    #[test]
    fn skip_empty_ranges() {
        let mut set = RangeSet::new();
        assert!(!set.insert(2..2));
        assert_eq!(set.len(), 0);
        assert!(!set.insert(4..4));
        assert_eq!(set.len(), 0);
        assert!(!set.insert(0..0));
        assert_eq!(set.len(), 0);
    }
}

#[cfg(test)]
mod compact_tests {
    use super::*;

    #[test]
    fn merge_and_split() {
        let mut set = CompactRangeSet::new();
        assert!(set.insert(0..2));
        assert!(set.insert(2..4));
        assert!(!set.insert(1..3));
        assert_eq!(set.len(), 1);
        assert_eq!(&set.elts().collect::<Vec<_>>()[..], [0, 1, 2, 3]);
        assert!(!set.contains(4));
        assert!(set.remove(2..3));
        assert_eq!(set.len(), 2);
        assert!(!set.contains(2));
        assert_eq!(&set.elts().collect::<Vec<_>>()[..], [0, 1, 3]);
    }

    #[test]
    fn double_merge_exact() {
        let mut set = CompactRangeSet::new();
        assert!(set.insert(0..2));
        assert!(set.insert(4..6));
        assert_eq!(set.len(), 2);
        assert!(set.insert(2..4));
        assert_eq!(set.len(), 1);
        assert_eq!(&set.elts().collect::<Vec<_>>()[..], [0, 1, 2, 3, 4, 5]);
    }

    #[test]
    fn single_merge_low() {
        let mut set = CompactRangeSet::new();
        assert!(set.insert(0..2));
        assert!(set.insert(4..6));
        assert_eq!(set.len(), 2);
        assert!(set.insert(2..3));
        assert_eq!(set.len(), 2);
        assert_eq!(&set.elts().collect::<Vec<_>>()[..], [0, 1, 2, 4, 5]);
    }

    #[test]
    fn single_merge_high() {
        let mut set = CompactRangeSet::new();
        assert!(set.insert(0..2));
        assert!(set.insert(4..6));
        assert_eq!(set.len(), 2);
        assert!(set.insert(3..4));
        assert_eq!(set.len(), 2);
        assert_eq!(&set.elts().collect::<Vec<_>>()[..], [0, 1, 3, 4, 5]);
    }

    #[test]
    fn double_merge_wide() {
        let mut set = CompactRangeSet::new();
        assert!(set.insert(0..2));
        assert!(set.insert(4..6));
        assert_eq!(set.len(), 2);
        assert!(set.insert(1..5));
        assert_eq!(set.len(), 1);
        assert_eq!(&set.elts().collect::<Vec<_>>()[..], [0, 1, 2, 3, 4, 5]);
    }

    #[test]
    fn double_remove() {
        let mut set = CompactRangeSet::new();
        assert!(set.insert(0..2));
        assert!(set.insert(4..6));
        assert!(set.remove(1..5));
        assert_eq!(set.len(), 2);
        assert_eq!(&set.elts().collect::<Vec<_>>()[..], [0, 5]);
    }

    #[test]
    fn insert_multiple() {
        let mut set = CompactRangeSet::new();
        assert!(set.insert(0..1));
        assert!(set.insert(2..3));
        assert!(set.insert(4..5));
        assert!(set.insert(0..5));
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn remove_multiple() {
        let mut set = CompactRangeSet::new();
        assert!(set.insert(0..1));
        assert!(set.insert(2..3));
        assert!(set.insert(4..5));
        assert!(set.remove(0..5));
        assert!(set.is_empty());
    }

    // #[test]
    // fn replace_contained() {
    //     let mut set = CompactRangeSet::new();
    //     set.insert(2..4);
    //     assert_eq!(set.replace(1..5).collect::<Vec<_>>(), &[2..4]);
    //     assert_eq!(set.len(), 1);
    //     assert_eq!(set.peek_min().unwrap(), 1..5);
    // }

    // #[test]
    // fn replace_contains() {
    //     let mut set = CompactRangeSet::new();
    //     set.insert(1..5);
    //     assert_eq!(set.replace(2..4).collect::<Vec<_>>(), &[2..4]);
    //     assert_eq!(set.len(), 1);
    //     assert_eq!(set.peek_min().unwrap(), 1..5);
    // }

    // #[test]
    // fn replace_pred() {
    //     let mut set = CompactRangeSet::new();
    //     set.insert(2..4);
    //     assert_eq!(set.replace(3..5).collect::<Vec<_>>(), &[3..4]);
    //     assert_eq!(set.len(), 1);
    //     assert_eq!(set.peek_min().unwrap(), 2..5);
    // }

    // #[test]
    // fn replace_succ() {
    //     let mut set = CompactRangeSet::new();
    //     set.insert(2..4);
    //     assert_eq!(set.replace(1..3).collect::<Vec<_>>(), &[2..3]);
    //     assert_eq!(set.len(), 1);
    //     assert_eq!(set.peek_min().unwrap(), 1..4);
    // }

    // #[test]
    // fn replace_exact_pred() {
    //     let mut set = CompactRangeSet::new();
    //     set.insert(2..4);
    //     assert_eq!(set.replace(4..6).collect::<Vec<_>>(), &[]);
    //     assert_eq!(set.len(), 1);
    //     assert_eq!(set.peek_min().unwrap(), 2..6);
    // }

    // #[test]
    // fn replace_exact_succ() {
    //     let mut set = CompactRangeSet::new();
    //     set.insert(2..4);
    //     assert_eq!(set.replace(0..2).collect::<Vec<_>>(), &[]);
    //     assert_eq!(set.len(), 1);
    //     assert_eq!(set.peek_min().unwrap(), 0..4);
    // }

    #[test]
    fn skip_empty_ranges() {
        let mut set = CompactRangeSet::new();
        assert!(!set.insert(2..2));
        assert_eq!(set.len(), 0);
        assert!(!set.insert(4..4));
        assert_eq!(set.len(), 0);
        assert!(!set.insert(0..0));
        assert_eq!(set.len(), 0);
    }
}
