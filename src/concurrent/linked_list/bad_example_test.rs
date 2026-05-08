use verus_state_machines_macros::tokenized_state_machine;
use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::set::*;
use vstd::tokens::ElementToken;

verus! {

tokenized_state_machine!{
    machine {
        fields {
            #[sharding(set)]
            pub bools: Set<bool>,

            #[sharding(variable)]
            pub init_b: bool,
        }

        #[invariant]
        pub fn main_inv(&self) -> bool {
            (
                !self.init_b ==> self.bools.is_empty()
            ) &&
            (
                self.init_b ==>
                    (self.bools.contains(true) <==> !self.bools.contains(false)) &&
                    (self.bools.contains(true) || self.bools.contains(false))
            )
        }

        init!{
            initialize()
            {
                init bools = Set::empty();
                init init_b = false;
            }
        }

        transition!{
            add_true()
            {
                require(!pre.init_b);
                update init_b = true;
                add bools += set { true };
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { 
        }

        #[inductive(add_true)]
        fn add_true_inductive(pre: Self, post: Self) { 
        }

        property!{
            have_true() {
                have bools >= set { true };
                birds_eye let s = pre.bools;

                assert(s.contains(true) <==> !s.contains(false));
                assert(!s.contains(false));
            }
        }
    }
}

fn main() { 
    let tracked (
        Tracked(instance),
        Tracked(bools),
        Tracked(init_b),
    ) = machine::Instance::initialize();

    let tracked true_token;
    proof {
        true_token = instance.add_true(&mut init_b);
        instance.have_true(&true_token);
        assert(
            !(
                exists |token: machine::bools|
                    token.instance_id() == instance.id() &&
                    token.element() == false
            )
        )
    }
}
}