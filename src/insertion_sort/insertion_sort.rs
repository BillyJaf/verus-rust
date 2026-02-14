pub fn insertion_sort(arr: &mut [i32]) {
    let num_elements = arr.len();
    
    // Do this check so that later we can cast to an i32 safely.
    if num_elements > (i32::MAX) as usize {
        println!("Array is too large to sort. Array length: {}", arr.len());
        return;
    }

    let mut i = 1;

    while i < num_elements {
        let mut j = i;
        while j > 0  && arr[j - 1] > arr[j] 
        {   
            let temp = arr[j];
            arr[j] = arr[j - 1];
            arr[j - 1] = temp;
            j -= 1;
        }
        i += 1;
    }
}