//! An implementation of the MJRTY algorithm described by Boyer and Moore
//! in "MJRTY - A Fast Majority Vote Algorithm."
//!
//! https://www.cs.utexas.edu/~moore/best-ideas/mjrty/index.html

use std::cmp::Eq;

#[allow(dead_code)]
pub fn majority_element<I>(elements: I) -> Option<I::Item>
where
    I: Iterator + Clone,
    I::Item: Eq,
{
    let mut confidence = 0;
    let mut option_winner = None;

    for elem in elements.clone() {
        // update `option_winner` using the MJRTY update rules
        option_winner = if let Some(winner) = option_winner {
            if winner == elem {
                // found a match, increment `confidence`
                confidence += 1;
                Some(winner)
            } else if confidence > 1 {
                // not a match, but `confidence` is still positive
                confidence -= 1;
                Some(winner)
            } else {
                // not a match, `confidence` is `0`
                confidence = 0;
                None
            }
        } else {
            // we don't have a guess, so set `option_winner` to the current element
            confidence = 1;
            Some(elem)
        }
    }

    if let Some(winner) = option_winner {
        // do one more pass to make sure we don't have a false positive
        let mut matches = 0;
        let mut total = 0;
        for elem in elements {
            if elem == winner {
                matches += 1;
            }
            total += 1;
        }

        if matches > total / 2 {
            return Some(winner);
        }
    }
    None
}

#[cfg(test)]
mod test {
    use super::majority_element;

    #[test]
    fn ints() {
        let ints = vec![1, 2, 1, 3, 1, 4, 3, 2, 1, 1, 1];
        let winner = majority_element(ints.iter());
        assert_eq!(winner, Some(&1));
    }

    #[test]
    fn no_winner() {
        let strings = vec![
            "a".to_string(),
            "b".to_string(),
            "c".to_string(),
            "a".to_string(),
            "c".to_string(),
        ];
        let winner = majority_element(strings.iter());
        assert_eq!(winner, None);
    }

    #[test]
    fn tie() {
        let bools = vec![true, true, false, true, false, false];
        let winner = majority_element(bools.iter());
        assert_eq!(winner, None);
    }
}
