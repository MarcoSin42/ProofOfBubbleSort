import Init.Data.Basic

set_option pp.raw true
set_option pp.raw.maxDepth 10

abbrev ℕ : Type := Nat

def is_ge (x y : ℕ) : Bool :=
  if x ≥ y then true
  else false

def is_sorted : List ℕ → Bool
| [] => true -- Trivially, an empty list is sorted
| [x] => true -- Trivially, a singleton is sorted
-- We have that a list is sorted iff it's first two elements are sorted
-- and the tail of the list is sorted
| x::y::xs => is_ge x y ∧ is_sorted (y :: xs)

def sorted_list : List ℕ := [1, 2, 3, 4, 5].reverse
def unsorted_list : List ℕ := [54, 5, 3, 32, 12,1, 2].reverse
#eval is_sorted sorted_list
#eval is_sorted unsorted_list

def bubble_down : List ℕ → List ℕ
| [] => []
| (x::xs) =>
  (List.foldl (λ acc x1 =>
    match acc with
    | [] => [x1]
    | (x2::rest) =>
        if x2 < x1 then x2::x1::rest
        else x1::x2::rest
    ) [x] xs).reverse


def bubble_sort (lst : List ℕ) : List ℕ :=
  match (lst.length, lst) with
  | (0,_) => []
  | (1,x) => x
  | (_,lst) =>
    let pass := bubble_down lst
    match (pass == lst, pass) with
    | (true,_) => lst
    | (false,x::xs) =>
        /- W.T.S. This terminates eventually. by
        W.T.S sizeof(xs) < sizeOf(lst) → This algorithm terminates
        ∵ pass = x::xs and sizeOf(pass) == sizeOf(lst)
        → sizeOf(x::xs) = sizeOf(lst)
        → sizeOf(xs) < sizeOf(x::xs) = sizeOf(lst)
        → sizeOf(xs) < sizeOf(lst)

        ∴ This algorithm will terminate
        -/
        have size_pass_eq_lst : sizeOf lst = sizeOf pass := by
          have pass_eq_xxs : pass = x::xs := by
            sorry

        have terminates: sizeOf lst < sizeOf xs := by sorry
        bubble_sort pass
    | (false,[]) => []


#eval! bubble_sort [4, 5, 3, 2,42]

--#eval (bubble_sort unsorted_list).reverse
  -- if lst.length ≤ 1 then
  --   lst
  -- else
  --   if bubble_down lst = lst then bubble_down lst
  --   else bubble_down (bubble_down lst)
