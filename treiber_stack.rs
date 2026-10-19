#![cfg_attr(verus_keep_ghost, verifier::exec_allows_no_decreases_clause)]
use std::sync::Arc;
use verus_builtin::*;
use verus_builtin_macros::*;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::{atomic_ghost::*, pervasive::*, prelude::*, simple_pptr::*};

//
// Verified with Verus Version: 0.2026.08.30.b432e82
//


verus! {

//////////////////////////////////////////////////////////////////
//////////////////////// Type Definitions ////////////////////////
//////////////////////////////////////////////////////////////////
    
global layout StackCell is size == 16;

type StackCellAddress = usize;

//////////////////////////////////////////////////////////////////
/////////// Current Stack Representation Specfications ///////////
//////////////////////////////////////////////////////////////////
    
pub open spec fn no_duplicates(current_stack_addresses: Seq<StackCellAddress>) -> bool {
    current_stack_addresses.no_duplicates()
}

pub open spec fn current_stack_disjoint_to_popped(
    current_stack_addresses: Seq<StackCellAddress>,
    popped_addresses: Set<StackCellAddress>,
) -> bool {
    current_stack_addresses.to_set().disjoint(popped_addresses)
}

pub open spec fn current_stack_union_popped_is_all_addresses(
    current_stack_addresses: Seq<StackCellAddress>,
    popped_addresses: Set<StackCellAddress>,
    all_addresses: Set<StackCellAddress>,
) -> bool {
    current_stack_addresses.to_set().union(popped_addresses) == all_addresses
}

pub open spec fn current_stack_contains_base_address(
    current_stack_addresses: Seq<StackCellAddress>,
    base_address: StackCellAddress,
) -> bool {
    current_stack_addresses.contains(base_address) && current_stack_addresses.first()
        == base_address
}

pub open spec fn current_stack_has_witnesses<V>(
    current_stack_addresses: Seq<StackCellAddress>,
    witnesses: Map<StackCellAddress, V>,
) -> bool {
    current_stack_addresses.to_set().subset_of(witnesses.dom())
}

//////////////////////////////////////////////////////////////////
////////////// Witness and Permission Specfications //////////////
//////////////////////////////////////////////////////////////////
pub open spec fn addresses_reflect_witnesses<V>(
    all_addresses: Set<StackCellAddress>,
    witnesses: Map<StackCellAddress, V>,
) -> bool {
    all_addresses == witnesses.dom()
}

pub open spec fn witnesses_reflect_permissions(
    witnesses: Map<StackCellAddress, PointsTo<StackCell>>,
    permissions: Map<StackCellAddress, PointsTo<StackCell>>,
) -> bool {
    witnesses == permissions
}

pub open spec fn base_address_witness_exists(
    base_address: StackCellAddress,
    witnesses: Map<StackCellAddress, PointsTo<StackCell>>,
) -> bool {
    witnesses.dom().contains(base_address)
}

pub open spec fn maps_are_structured_correctly(
    witnesses: Map<StackCellAddress, PointsTo<StackCell>>,
    permissions: Map<StackCellAddress, PointsTo<StackCell>>,
) -> bool {
    forall|addr: StackCellAddress|
        #![auto]
        (witnesses.dom().contains(addr) ==> witnesses.index(addr).addr() == addr) && (
        permissions.dom().contains(addr) ==> permissions.index(addr).addr() == addr)
}

pub open spec fn witnesses_contains_next_witness(
    base_address: StackCellAddress,
    witnesses: Map<StackCellAddress, PointsTo<StackCell>>,
) -> bool {
    forall|addr: StackCellAddress|
        #![auto]
        (witnesses.dom().contains(addr) && addr != base_address) ==> (witnesses.dom().contains(
            witnesses.index(addr).value().next_address,
        ))
}

pub open spec fn permissions_are_init_except_base(
    base_address: StackCellAddress,
    permissions: Map<StackCellAddress, PointsTo<StackCell>>,
) -> bool {
    forall|addr: StackCellAddress|
        #![auto]
        permissions.dom().contains(addr) ==> (addr != base_address <==> permissions.index(
            addr,
        ).is_init())
}

//////////////////////////////////////////////////////////////////
/////////// Tokenised State Machine Instance Checker /////////////
//////////////////////////////////////////////////////////////////
pub open spec fn from_the_correct_tsm<T>(
    instance: treiber_stack::Instance,
    token: impl ValueToken<T>,
) -> bool {
    instance.id() == token.instance_id()
}

pub open spec fn from_the_correct_tsm_kv<K, V>(
    instance: treiber_stack::Instance,
    token: impl KeyValueToken<K, V>,
) -> bool {
    instance.id() == token.instance_id()
}

//////////////////////////////////////////////////////////////////
//////////////////// Tokenised State Machine /////////////////////
//////////////////////////////////////////////////////////////////

tokenized_state_machine!{
    treiber_stack {
        fields {
            // Book Keeping

            #[sharding(constant)]
            pub base_address: StackCellAddress,

            // Stack Representation

            #[sharding(variable)]
            pub current_stack_addresses: Seq<StackCellAddress>,

            #[sharding(variable)]
            pub popped_addresses: Set<StackCellAddress>,

            // Everything Ever in the Stack

            #[sharding(variable)]
            pub all_addresses: Set<StackCellAddress>,

            // Witnesses and Permissions

            #[sharding(persistent_map)]
            pub witnesses: Map<StackCellAddress, PointsTo<StackCell>>,

            #[sharding(storage_map)]
            pub permissions: Map<StackCellAddress, PointsTo<StackCell>>
        }

        // Current Stack Representation Invariants

        #[invariant]
        pub fn no_duplicates_inv(&self) -> bool {
            no_duplicates(
                self.current_stack_addresses
            )
        }

        #[invariant]
        pub fn current_stack_disjoint_to_popped_inv(&self) -> bool {
            current_stack_disjoint_to_popped(
                self.current_stack_addresses,
                self.popped_addresses
            )
        }

        #[invariant]
        pub fn current_stack_union_popped_is_all_addresses_inv(&self) -> bool {
            current_stack_union_popped_is_all_addresses(
                self.current_stack_addresses,
                self.popped_addresses,
                self.all_addresses
            )
        }

        #[invariant]
        pub fn current_stack_contains_base_address_inv(&self) -> bool {
            current_stack_contains_base_address(
                self.current_stack_addresses,
                self.base_address
            )
        }

        #[invariant]
        pub fn current_stack_has_witnesses_inv(&self) -> bool {
            current_stack_has_witnesses(
                self.current_stack_addresses,
                self.witnesses
            )
        }

        #[invariant]
        pub fn addresses_reflect_witnesses_inv(&self) -> bool {
            addresses_reflect_witnesses(
                self.all_addresses,
                self.permissions
            )
        }

        #[invariant]
        pub fn witnesses_reflect_permissions_inv(&self) -> bool {
            witnesses_reflect_permissions(
                self.witnesses,
                self.permissions
            )
        }

        #[invariant]
        pub fn base_address_witness_exists_inv(&self) -> bool {
            base_address_witness_exists(
                self.base_address,
                self.witnesses
            )
        }

        #[invariant]
        pub fn maps_are_structured_correctly_inv(&self) -> bool {
            maps_are_structured_correctly(
                self.witnesses,
                self.permissions
            )
        }

        #[invariant]
        pub fn witnesses_contains_next_witness_inv(&self) -> bool {
            witnesses_contains_next_witness(
                self.base_address,
                self.witnesses
            )
        }

        #[invariant]
        pub fn permissions_are_init_except_base_inv(&self) -> bool {
            permissions_are_init_except_base(
                self.base_address,
                self.permissions
            )
        }

        init!{
            initialise(base_permission: PointsTo<StackCell>)
            {
                require(base_permission.is_uninit());

                init base_address            = base_permission.addr();
                init popped_addresses        = Set::empty();
                init current_stack_addresses = Seq::empty().push(base_permission.addr());
                init all_addresses           = Set::empty().insert(base_permission.addr());
                init witnesses               = Map::empty().insert(base_permission.addr(), base_permission);
                init permissions             = Map::empty().insert(base_permission.addr(), base_permission);
            }
        }

        transition!{
            push(new_stack_cell_permission: PointsTo<StackCell>)
            {
                require(new_stack_cell_permission.is_init());
                require(pre.current_stack_addresses.last() == new_stack_cell_permission.value().next_address);
                require(!pre.all_addresses.contains(new_stack_cell_permission.addr()));

                update all_addresses           = pre.all_addresses.insert(new_stack_cell_permission.addr());
                update current_stack_addresses = pre.current_stack_addresses.push(new_stack_cell_permission.addr());

                deposit permissions           += [new_stack_cell_permission.addr() => new_stack_cell_permission];
                add witnesses           (union)= [new_stack_cell_permission.addr() => new_stack_cell_permission];
            }
        }

        transition!{
            pop(current_top_permission: PointsTo<StackCell>)
            {
                require(current_top_permission.addr() != pre.base_address);
                require(pre.current_stack_addresses.last() == current_top_permission.addr());

                have witnesses                >= [current_top_permission.addr() => current_top_permission];
                update popped_addresses        = pre.popped_addresses.insert(pre.current_stack_addresses.last());
                update current_stack_addresses = pre.current_stack_addresses.drop_last();
            }
        }

        property!{
            get_permission_reference(
                stack_cell_address: StackCellAddress,
                stack_cell_permission: PointsTo<StackCell>
            ) {
                have witnesses    >= [stack_cell_address => stack_cell_permission];
                guard permissions >= [stack_cell_address => stack_cell_permission];
            }
        }

        property!{
            same_address_implies_same_permission(
                stack_cell_permission_1: PointsTo<StackCell>,
                stack_cell_permission_2: PointsTo<StackCell>
            ) {
                require(stack_cell_permission_1.addr() == stack_cell_permission_2.addr());

                have witnesses    >= [stack_cell_permission_1.addr() => stack_cell_permission_1];
                have witnesses    >= [stack_cell_permission_2.addr() => stack_cell_permission_2];

                assert(stack_cell_permission_1 == stack_cell_permission_2);
            }
        }

        #[inductive(initialise)]
        fn initialise_inductive(
            post: Self,
            base_permission: PointsTo<StackCell>
        ) {
            assert(post.current_stack_addresses.first() == post.base_address);
            assert(post.current_stack_addresses.to_set().union(post.popped_addresses) == post.all_addresses);
            assert(post.witnesses.index(post.base_address).is_uninit());
        }

        #[inductive(push)]
        fn push_inductive(
            pre: Self,
            post: Self,
            new_stack_cell_permission: PointsTo<StackCell>
        ) {
            assert(pre.current_stack_addresses == post.current_stack_addresses.drop_last());
            assert(post.current_stack_addresses.last() == new_stack_cell_permission.addr());
            assert(post.current_stack_addresses.to_set().union(post.popped_addresses) == post.all_addresses);
        }

        #[inductive(pop)]
        fn pop_inductive(
            pre: Self,
            post: Self,
            current_top_permission: PointsTo<StackCell>
        ) {
            assert(pre.current_stack_addresses.drop_last().push(current_top_permission.addr()) == pre.current_stack_addresses);
            assert(
                pre.current_stack_addresses.to_set()
                                           .union(pre.popped_addresses) ==
                post.current_stack_addresses.to_set()
                                            .union(post.popped_addresses)
            );
        }
    }
}

//////////////////////////////////////////////////////////////////
///////////////////// Struct With Invariants /////////////////////
//////////////////////////////////////////////////////////////////
pub tracked struct TreiberStackTokens {
    pub current_stack_addresses: treiber_stack::current_stack_addresses,
    pub popped_addresses: treiber_stack::popped_addresses,
    pub all_addresses: treiber_stack::all_addresses,
    pub witnesses: Map<StackCellAddress, treiber_stack::witnesses>,
}

#[derive(Copy, Clone)]
pub struct StackCell {
    pub elem: u32,
    pub next_address: StackCellAddress,
}

struct_with_invariants!{
    pub struct TreiberStack {
        pub base_address: StackCellAddress,
        pub top_address: AtomicUsize<_, TreiberStackTokens, _>,
        pub instance: Tracked<treiber_stack::Instance>
    }

    pub open spec fn valid(self) -> bool {
        invariant on top_address with (base_address, instance) is (top_addr: usize, tokens: TreiberStackTokens) {
            &&& base_address == instance.base_address()

            //////////////////////////////////////////////////////////////////
            //////////////// Tokens Come From the Correct TSM ////////////////
            //////////////////////////////////////////////////////////////////

            &&& from_the_correct_tsm(instance@, tokens.current_stack_addresses)
            &&& from_the_correct_tsm(instance@, tokens.popped_addresses)
            &&& from_the_correct_tsm(instance@, tokens.all_addresses)
            &&& forall |addr: StackCellAddress| #![auto]
                    tokens.witnesses.dom().contains(addr) ==>
                        from_the_correct_tsm_kv(instance@, tokens.witnesses.index(addr))

            //////////////////////////////////////////////////////////////////
            ////////////////// Local Correctness Invariants //////////////////
            //////////////////////////////////////////////////////////////////

            &&& tokens.witnesses.dom().contains(top_addr)
            &&& tokens.current_stack_addresses.value().contains(top_addr)
            &&& tokens.current_stack_addresses.value().last() == top_addr
            &&& top_addr == base_address <==> tokens.current_stack_addresses.value().len() == 1

            //////////////////////////////////////////////////////////////////
            /////////////// Transferable TSM Global Invariants ///////////////
            //////////////////////////////////////////////////////////////////

            &&& current_stack_contains_base_address(
                    tokens.current_stack_addresses.value(),
                    base_address
                )
            &&& no_duplicates(tokens.current_stack_addresses.value())
            &&& current_stack_disjoint_to_popped(
                    tokens.current_stack_addresses.value(),
                    tokens.popped_addresses.value()
                )
            &&& current_stack_union_popped_is_all_addresses(
                    tokens.current_stack_addresses.value(),
                    tokens.popped_addresses.value(),
                    tokens.all_addresses.value()
                )
            &&& current_stack_has_witnesses(
                    tokens.current_stack_addresses.value(),
                    tokens.witnesses
                )
            &&& addresses_reflect_witnesses(
                    tokens.all_addresses.value(),
                    tokens.witnesses
                )

            //////////////////////////////////////////////////////////////////
            ///////////////// Witness-Map-Specific Invariants ////////////////
            //////////////////////////////////////////////////////////////////

            // Asserts the map has correct structure.
            // Heavily resembles `maps_are_structured_correctly`, cannot use
            // it directly due to the `Map` structure of `tokens.witnesses`:
            &&& forall |addr: StackCellAddress| #![auto]
                    tokens.witnesses.dom().contains(addr) ==> (
                        tokens.witnesses.index(addr).key() == addr &&
                        tokens.witnesses.index(addr).value().addr() == addr
                    )

            // Asserts the map always contains `base_address`.
            // Heavily resembles `base_address_witness_exists`, cannot use
            // it directly due to the `Map` structure of `tokens.witnesses`:
            &&& tokens.witnesses.dom().contains(base_address)

            // Asserts that all witness tokens are witnesses of permissions
            // that point to initialised memory except for the base witness.
            // Heavily resembles `permissions_are_init_except_base`, cannot use
            // it directly due to the `Map` structure of `tokens.witnesses`:
            &&& forall |addr: StackCellAddress| #![auto]
                    tokens.witnesses.dom().contains(addr) ==> (
                        addr != base_address <==> tokens.witnesses.index(addr).value().is_init()
                    )

            // Asserts that every witness token is pointed to by another witness
            // token, with the exception of the base witness.
            // Heavily resembles `witnesses_contains_next_witness`, cannot use
            // it directly due to the `Map` structure of `tokens.witnesses`:
            &&& forall |addr: StackCellAddress| #![auto]
                    (
                        tokens.witnesses.dom().contains(addr) &&
                        addr != base_address
                    ) ==> (
                        tokens.witnesses.dom().contains(
                            tokens.witnesses.index(addr).value().value().next_address
                        )
                    )

            //////////////////////////////////////////////////////////////////
            //////////////// Correct Stack Ordering Invariant ////////////////
            //////////////////////////////////////////////////////////////////

            // Asserts that in the stack representation, each element (except base)
            // points to the next stack cell that is equal to its witness token's
            // next stack cell. Essentially, the stack is correctly ordered.
            &&& forall |i: int| #![auto]
                    0 < i < tokens.current_stack_addresses.value().len() ==> (
                        tokens.current_stack_addresses.value()[i-1] ==
                        tokens.witnesses.index(
                            tokens.current_stack_addresses.value()[i]
                        ).value().value().next_address
                    )
        }
    }
}

//////////////////////////////////////////////////////////////////
///////////////////////// Implementation /////////////////////////
//////////////////////////////////////////////////////////////////
impl TreiberStack {
    pub fn new() -> (treiber_stack: Self)
        ensures
            treiber_stack.valid(),
    {
        let (base, Tracked(base_perm)) = PPtr::<StackCell>::empty();
        let base_address = base.addr();

        let tracked permissions = Map::tracked_empty();
        proof {
            permissions.tracked_insert(base_address, base_perm);
        }

        let tracked (
            Tracked(instance),
            Tracked(current_stack_addresses),
            Tracked(popped_addresses),
            Tracked(all_addresses),
            Tracked(witnesses),
        ) = treiber_stack::Instance::initialise(base_perm, permissions);

        let tracked witnesses = witnesses.into_map();

        let tracked treiber_stack_tokens = TreiberStackTokens {
            current_stack_addresses,
            popped_addresses,
            all_addresses,
            witnesses,
        };

        assert(current_stack_addresses.value().first() == base_address);
        assert(treiber_stack_tokens.current_stack_addresses.value().to_set().union(
            treiber_stack_tokens.popped_addresses.value(),
        ) == Set::empty().insert(base_address));

        let top_address = AtomicUsize::new(
            Ghost((base_address, Tracked(instance))),
            base_address,
            Tracked(treiber_stack_tokens),
        );

        Self { base_address, top_address, instance: Tracked(instance) }
    }

    //////////////////////////////////////////////////////////////////
    ////////////////////// Push Implementation ///////////////////////
    //////////////////////////////////////////////////////////////////
    pub fn push(&self, elem: u32)
        requires
            self.valid(),
        ensures
            self.valid(),
    {
        loop
            invariant
                self.valid(),
        {
            let new_stack_cell = StackCell { elem, next_address: self.top_address.load() };
            let (permission_guarded_new_stack_cell, Tracked(new_stack_cell_permission)) = PPtr::new(
                new_stack_cell,
            );

            //////////////////////////////////////////////////////////////////
            /////////////////////// Atomic With Ghost ////////////////////////
            //////////////////////////////////////////////////////////////////
            let push_result =
                atomic_with_ghost!(
                self.top_address => compare_exchange(
                        permission_guarded_new_stack_cell.read(Tracked(&new_stack_cell_permission)).next_address,
                        permission_guarded_new_stack_cell.addr()
                    );

                returning previous_head_address_result;

                ghost treiber_stack_tokens => {
                    if let Ok(_) = previous_head_address_result {

                        // Proof that the TSM cannot already hold a PointsTo permission for
                        // the newly constructed cell:
                        if treiber_stack_tokens.witnesses.dom().contains(new_stack_cell_permission.addr()) {
                            let tracked token_from_atomic = treiber_stack_tokens.witnesses
                                                                                .tracked_borrow(new_stack_cell_permission.addr());
                            let tracked perm_ref_from_tsm = self.instance.get_permission_reference(
                                                                token_from_atomic.key(),
                                                                token_from_atomic.value(),
                                                                &token_from_atomic
                                                            );
                            // Contradiction
                            new_stack_cell_permission.is_distinct(perm_ref_from_tsm);
                            assert(false);
                        }

                        let ghost pre_current_stack_addresses = treiber_stack_tokens.current_stack_addresses.value();
                        let ghost pre_popped_addresses = treiber_stack_tokens.popped_addresses.value();

                        let tracked new_witness_token = self.instance.push(
                            new_stack_cell_permission,
                            &mut treiber_stack_tokens.current_stack_addresses,
                            &mut treiber_stack_tokens.all_addresses,
                            new_stack_cell_permission
                        );

                        assert(pre_current_stack_addresses =~= pre_current_stack_addresses.push(new_witness_token.value().addr()).drop_last());

                        treiber_stack_tokens.witnesses.tracked_insert(new_witness_token.key(), new_witness_token);

                        assert(treiber_stack_tokens.current_stack_addresses.value().last() == new_witness_token.key());
                        assert(
                            pre_current_stack_addresses.to_set().union(pre_popped_addresses).insert(new_witness_token.key()) ==
                            treiber_stack_tokens.current_stack_addresses.value().to_set().union(treiber_stack_tokens.popped_addresses.value())
                        );
                    }
                }
            );

            if let Ok(_) = push_result {
                return;
            }
        }
    }

    //////////////////////////////////////////////////////////////////
    ////////////////////// Pop Implementation ////////////////////////
    //////////////////////////////////////////////////////////////////
    pub fn pop(&self) -> (elem: Option<u32>)
        requires
            self.valid(),
        ensures
            self.valid(),
    {
        loop
            invariant
                self.valid(),
        {
            let tracked stack_head_witness;
            let tracked stack_cell_permission_reference;

            let top_address =
                atomic_with_ghost!(
                self.top_address => load();

                returning addr;

                ghost treiber_stack_tokens => {
                    stack_head_witness = *treiber_stack_tokens.witnesses.tracked_borrow(addr);
                }
            );

            if (top_address == self.base_address) {
                return None;
            }
            proof {
                stack_cell_permission_reference =
                self.instance.get_permission_reference(
                    stack_head_witness.key(),
                    stack_head_witness.value(),
                    &stack_head_witness,
                );
            }

            let permissioned_pointer = PPtr::<StackCell>::from_addr(top_address);
            let top_stack_cell = permissioned_pointer.read(
                Tracked(stack_cell_permission_reference),
            );

            //////////////////////////////////////////////////////////////////
            /////////////////////// Atomic With Ghost ////////////////////////
            //////////////////////////////////////////////////////////////////
            let new_stack_head_address_result =
                atomic_with_ghost!(
                self.top_address => compare_exchange(
                    top_address,
                    top_stack_cell.next_address
                );

                update current_stack_head_address -> new_stack_head_address;
                returning previous_head_address_result;

                ghost treiber_stack_tokens => {
                    if let Ok(_) = previous_head_address_result {

                        let tracked equal_witness = *treiber_stack_tokens.witnesses.tracked_borrow(current_stack_head_address);
                        self.instance.same_address_implies_same_permission(
                            stack_head_witness.value(),
                            equal_witness.value(),
                            &stack_head_witness,
                            &equal_witness
                        );

                        assert(treiber_stack_tokens.current_stack_addresses.value() =~= treiber_stack_tokens.current_stack_addresses.value().drop_last().push(current_stack_head_address));

                        let ghost pre_current_stack_addresses = treiber_stack_tokens.current_stack_addresses.value();
                        let ghost pre_popped_addresses = treiber_stack_tokens.popped_addresses.value();

                        self.instance.pop(
                            stack_head_witness.value(),
                            &mut treiber_stack_tokens.current_stack_addresses,
                            &mut treiber_stack_tokens.popped_addresses,
                            &stack_head_witness
                        );

                        assert(
                            pre_current_stack_addresses.to_set().union(pre_popped_addresses) ==
                            treiber_stack_tokens.current_stack_addresses.value().to_set().union(treiber_stack_tokens.popped_addresses.value())
                        );
                    }
                }
            );

            if let Ok(new_stack_head_address) = new_stack_head_address_result {
                return Some(top_stack_cell.elem);
            }
        }
    }
}

pub fn main() {
}

} // verus!
