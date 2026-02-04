use vstd::prelude::*;

verus!{
    pub fn vec_remove_duplicates(input_vector: Vec<i32>) -> (output_vector: Vec<i32>) 
        ensures
            input_vector.len() >= output_vector.len(),
            forall |x: int| #[trigger] input_vector@.contains(x as i32) <==> output_vector@.contains(x as i32), 
            forall |i: int, j: int|
                (0 <= i < j < output_vector@.len()) ==> output_vector@.index(i) != output_vector@.index(j),
    {
        let mut current_output: Vec<i32> = Vec::new();
        let mut old_output: Vec<i32> = Vec::new();
        let mut i = 0;
        let mut last_checked_item: Option<i32> = None;

        while i < input_vector.len()
            invariant
                0 <= i,
                i <= input_vector.len(),
                current_output.len() <= input_vector.len(),
                i == 0 ==> last_checked_item == None::<i32>,
                i > 0 ==> (last_checked_item != None::<i32> && last_checked_item.unwrap() == input_vector@.index(i - 1 as int)),

                ((old_output.len() == current_output.len()) && 
                (forall |j: int| 0 <= j < current_output.len() ==> 
                old_output@.index(j) == current_output@.index(j)) &&
                (i > 0 ==> current_output@.contains(last_checked_item.unwrap()))) ||

                ((old_output.len() + 1 == current_output.len()) && 
                (forall |j: int| 0 <= j < old_output.len() ==> 
                old_output@.index(j) == current_output@.index(j)) &&
                current_output@.index(current_output.len() - 1) == last_checked_item.unwrap()),

                forall |j: int, k: int|
                    (0 <= j < k < current_output@.len()) ==> current_output@.index(j) != current_output@.index(k),
            decreases
                input_vector.len() - i
        {
            let current_item = input_vector.get(i).unwrap().clone();

            let mut is_duplicate = false;
            let mut j = 0;
            let current_output_clone = current_output.clone();
            while j < current_output.len() 
                invariant
                    0 <= j,
                    j <= current_output.len(),
                    current_output.len() == current_output_clone.len(),
                    forall |k: int| (0 <= k < current_output.len()) ==> current_output@.index(k) == current_output_clone@.index(k)
                decreases
                    current_output.len() - j
            {
                if current_output.get(j).unwrap().clone() == current_item {
                    is_duplicate = true;
                }
                j += 1;
            }

            old_output = current_output.clone();
            if !is_duplicate {
                current_output.push(current_item.clone());
            }
            last_checked_item = Some(current_item);
            i += 1;
        }


        current_output
    }
}