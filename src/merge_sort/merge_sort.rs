pub fn merge_sort_sequential<T>(arr: &mut [T])
    where T: Eq + PartialOrd + Copy
{
    let mid_point = arr.len() / 2;

    if mid_point == 0 {
        return;
    }

    let (left, right) = arr.split_at_mut(mid_point);
    merge_sort_sequential(left);
    merge_sort_sequential(right);

    let sorted = merge(left, right);
    arr.copy_from_slice(&sorted);
}

fn merge<T>(left: &[T], right: &[T]) -> Vec<T>
    where T: Eq + PartialOrd + Copy
{   
    let mut left_pointer = 0;
    let mut right_pointer = 0;
    let mut sorted_arr = Vec::with_capacity(left.len() + right.len());

    while left_pointer < left.len() && right_pointer < right.len() {
        if left[left_pointer] <= right[right_pointer] {
            sorted_arr.push(left[left_pointer]);
            left_pointer += 1;
        } else {
            sorted_arr.push(right[right_pointer]);
            right_pointer += 1;
        }
    }

    while left_pointer < left.len() {
        sorted_arr.push(left[left_pointer]);
        left_pointer += 1;
    }

    while right_pointer < right.len() {
        sorted_arr.push(right[right_pointer]);
        right_pointer += 1;
    }

    sorted_arr
}