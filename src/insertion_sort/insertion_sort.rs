pub fn insertion_sort(mut arr: Vec<i32>) -> Vec<i32> {
    let num_elements = arr.len();
    
    // Do this check so that later we can cast to an i32 safely.
    if num_elements > (u32::MAX >> 1) as usize {
        println!("Array is too large to sort. Array length: {}", arr.len());
        return arr;
    }

    for i in 1..num_elements {
        let current_element = arr[i];
        let mut j = (i - 1) as i32;
        while j >= 0  && arr[j as usize] >= current_element {
            arr[(j + 1) as usize] = arr[j as usize];
            j -= 1;
        }

        arr[(j + 1) as usize] = current_element;
    }
    return arr;
}