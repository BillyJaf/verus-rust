pub fn insertion_sort(arr: &mut [i32]) {
    for i in 1..arr.len() {
        let current_element = arr[i];
        let mut j = i - 1;
        while j > 0  && arr[j] >= current_element {
            arr[j + 1] = arr[j];
            j -= 1;
        }

        if j == 0 && arr[j] >= current_element {
            arr[1] = arr[0];
            arr[0] = current_element;
        } else {
            arr[j + 1] = current_element;
        }
    }
}