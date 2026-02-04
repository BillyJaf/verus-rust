pub fn remove_duplicates_fast(intput_vector: Vec<i32>) -> Vec<i32> {
    let mut output_vector = Vec::new();
    let mut seen_values: HashSet<i32> = HashSet::new();

    for element in intput_vector.into_iter() {
        if !seen_values.contains(&element) {
            seen_values.insert(element);
            output_vector.push(element);
        }
    }

    output_vector
}

pub fn remove_duplicates_slow(input_vector: Vec<i32>) -> Vec<i32> {
    let mut output_vector = Vec::new();
    let mut is_duplicate = false;

    for input_element in input_vector.into_iter() {
        for output_element in output_vector.iter() {
            if input_element == *output_element {
                is_duplicate = true;
                break;
            }
        }

        if !is_duplicate {
            output_vector.push(input_element)
        }
    }

    output_vector
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fast_duplicate_remove() {
        assert_eq!(remove_duplicates_fast(vec![1,2,3,4,5,5]), vec![1,2,3,4,5]);
    }

    #[test]
    fn test_slow_duplicate_remove() {
        assert_eq!(remove_duplicates_slow(vec![1,2,3,4,5,5]), vec![1,2,3,4,5]);
    }
}