pub fn insertion_sort(mut arr: Vec<i32>) -> Vec<i32> {
    let num_elements = arr.len();
    
    // Do this check so that later we can cast to an i32 safely.
    if num_elements > (i32::MAX) as usize {
        println!("Array is too large to sort. Array length: {}", arr.len());
        return arr;
    }

    let mut i = 1;

    while i < num_elements {
        let current_element = arr[i];
        let mut j = i as i32 - 1;
        while j >= 0  && arr[j as usize] > current_element 
        {
            arr[j as usize + 1] = arr[j as usize];
            arr[j as usize] = current_element;
            j -= 1;
        }
        i += 1;
    }
    return arr;
}