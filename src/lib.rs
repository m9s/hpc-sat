const CLAUSE_LEN : usize = 16;

use std::collections::{HashSet, HashMap};
use std::vec::Vec;
use std::ops;

/* Code will have big lists of following things:
 * - Clauses
 * - Literals set to TRUE
 * - Literals set to FALSE
 *
 * Going to pack into 32-bits for performance, limits maximum variables to 30-bits and clauses to ~30-bits
 * depending on the length of clauses.
 */

//type Lit = std::num::Wrapping<u32>;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Lit(u32);

impl ops::Not for Lit {
    type Output = Lit;

    #[inline]
    fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}

impl Lit {
    #[inline]
    pub fn new(var: u32, sign: bool) -> Lit {
        Lit(var + var + (sign as u32))
    }

    #[inline]
    fn var(self) -> u32 {
        self.0 >> 1
    }

    #[inline]
    fn sign(self) -> bool {
        self.0 & 1 > 0
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Val {
    True,
    False,
    Undef
}

impl std::ops::BitXor<bool> for Val {
    type Output = Self;

    fn bitxor(self, rhs: bool) -> Self {
        if rhs {
            self
        } else {
            match self {
                Val::True => Val::False,
                Val::False => Val::True,
                Val::Undef => Val::Undef
            }
        }
    }
}

enum Watch {
    Binary(Lit),
    Ternary(Lit, Lit),
    Normal(Lit, u32)
}


/* Clause struct is 64 bytes long. Clauses with 15 or fewer literals have 0 as last value.
 * Clauses with 16 literals have literal as last value. Larger sizes have ptr to next clause as last value.
 */
type Clause = [u32; 16];

/* Minimal watch structure
 * Three types of watches - Cache Conscious Data Structures for Boolean Satisfiability Solvers
 * - Normal clause -> First literal (or some TRUE literal), ptr to clause
 * - Binary clause -> other literal, [nothing]
 * - Ternary clause -> one other literal, other literal
 *
 * Code should tell them apart by checking the second value - if it is:
 *    zero => Binary clause
 *    clause ptr => Normal clause
 *    else => Ternary clause
 *
 * Way to make better use of space in binary clauses?? Or does it just become variable sized?
 * TODO: Do we need the ptr for the linked clause str?? Or we just set a bit to say - check next block.
 *  - No, we need it so clauses can be addressed by their address - head is at proper place, tail is in gaps.
 */
//struct Watch(u32, u32);

struct Problem {
    clauses: Vec<[u32; CLAUSE_LEN]>
}

struct Solver {
    assignments: Vec<Val>,
    watches: HashMap<u32, Vec<Watch>>
}

impl Solver {
    fn value(&self, l: Lit) -> Val {
        self.assignments[l.var() as usize] ^ l.sign()
    }

    fn propogate_normal(&self, current: Lit, blocker: Lit, clause: u32) {
        if self.value(blocker) == Val::True {
            // If blocking literal is true, then clause is true and we can skip.
            // Keep the current watch
            return;
        } else {
            // Load the clause from the ref
            // Make sure current literal is the second literal of the clause?? Swap first and second.

            // Check first literal of the clause (if first != blocker). If true then
            // Replace the watch with new watch using the first literal as the blocker.
            // Skip to next

            // Otherwise walk through clause from third (second is current which is false)
            // if value is not False (true or undef) then
            //   move this literal (K) to second pos, move current to gap
            //   push the watch (which existing blocking literal) to !K watchlist
            //   drop the current watch

            // Check if first is undef (previously only checked for True)
            // if undef then unit literal so propogate
            // keep the current watch

            // if false then conflict
            // handle the conflict, keep the current watch, keep all remaining watches
        }
    }

    fn propogate_binary(&self, current: Lit, other: Lit) {
        match self.value(other) {
            Val::False => 1,     // Conflict detected - backtrack
            Val::True => 2,      // Clause is true - skip to next - this clause needs to be kept or it won't exist
            Val::Undef => 3      // Unset - propogate it
        };
    }

    fn propogate_ternary(&self, current: Lit, first: Lit, second: Lit) {
        let firstVal = self.value(first);

        if firstVal == Val::True {
            // Next
        } else {
            match (firstVal, self.value(second)) {
                (_, Val::True) => return, //Next
                (Val::Undef, Val::Undef) => return, // Add watch to missing lit
                (Val::Undef, Val::False) => return, // Propagate first
                (Val::False, Val::Undef) => return, // Propagate second
                _ => return,                        // Conflict
            }
        }
    }
}

fn propogation(s: &mut Solver, lit: u32) -> bool {
    // Get the relevant watchlist
    let w = s.watches.remove(&lit).unwrap_or_default();

    // Process each item in the watch list

    // If Normal(block, clause) and blocker is set to true, then next watchlist item
    // Else either replace the watch with a new literal. Might be able to keep the watch with a different blocking literal
    // If get to end of clause without any true/undef then must be a conflict
    
    true
}

fn get_state(literal: u32) -> Option<bool> {
    Some(false)
}

fn analyse(clause: u32) {
    // get current clause
    // add activity if learnt for learnt gc

    // go through each literal and check the decision level and seen flags

    // select next clause to check
    // lots of logic here

    // create minimum conflict cause
}

// Clause might be ~a || b
// If a was just set to true then ~a is false and that implies b is true
// In the watchlist for a there will be a binary clause containing b
fn check_binary(other: u32) {
    let a = match get_state(other) {
        Some(false) => 1,     // Conflict detected - backtrack
        Some(true) => 2,      // Clause is true - skip to next - this clause needs to be kept or it won't exist
        None => 3             // Unset - propogate it
    };
}

// Clause might be a || b || c
// If a was just set to false, then load the ~a watchlist and find an entry containing b and c
// The other watch list item will be in ~b or ~c
fn check_tertiary(first: u32, second: u32) {
    let a = match (get_state(first), get_state(second)) {
        (Some(false), None) => 1,         // Propogate 'second'
        (None, Some(false)) => 1,         // Propogate 'first'
        (Some(true), _) => 1,             // Clause true - next??
        (_, Some(true)) => 1,             // Clause true - next??
        (Some(false), Some(false)) => 1,  // Conflict detected - backtrack
        (None, None) => 1,                // Add a watch to the unwatched of the two (second?)
    };
}

// Clause might be a || b || c || d
// If a was just set to false, then load the ~a watchlist and find an entry containing b and a ptr to clause
fn check_normal(first: u32, clause: u32) {
    let a = match get_state(first) {
        Some(false) => 1,     // Unhelpful - load clause and check next literal
        Some(true) => 2,      // Clause is true - skip to next
        None => 3             // Check watchlist for ~b for a ptr to our clause - if none, then add one (blocking literal is another one from the clause) - if already in watch list then load clause and look for another clause to add to watch list
    };

    // TODO is there a trick to ensure that 'first' s the other watched literal whenever get_state == None?
    // And also guarantee that other watched literal is non 'first' when state => false?
}

pub fn test() -> u32 {
    let b = Lit::new(3, false);
    let a = [0; CLAUSE_LEN];

    a[0]
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
