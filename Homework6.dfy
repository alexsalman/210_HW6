datatype Tree<T> = Leaf | Node(Tree<T>, Tree<T>, T)
datatype List<T> = Nil | Cons(T, List<T>)

function flatten<T>(tree:Tree<T>):List<T>
{
    match tree
    case Leaf => Nil
    case Node(left, right, t) => append(flatten(left), Cons(t,flatten(right)))
}

 function append<T>(xs:List<T>, ys:List<T>):List<T>
 decreases xs
 {
	match(xs)
    case Nil => ys
    case Cons(x, xs') => Cons(x, append(xs', ys))
}
//Cons takes a single element and stick it to a list
function treeContains<T>(tree:Tree<T>, element:T):bool
decreases tree
{
	match tree
    case Leaf => false
    case Node(left, right, t) => t == element || treeContains(left, t) || treeContains(right, t)
}
// Note that dafny doesn't quite understand that a == b is the same thing as a <==> b when they are booleans.
function listContains<T>(xs:List<T>, element:T):bool
{
	match xs
    case Nil => false
    case Cons(t, xs') => t == element || listContains(xs', element)
}

lemma sameElements<T>(tree:Tree<T>, element:T)
ensures treeContains(tree, element) <==> listContains(flatten(tree), element)
{
	// True => True
    // False => False
    // True x False
    // False x True
    match tree
    case Leaf => false
    case Node(left, right, t) => {
        sameElements(left, t);
        sameElements(right, t);
    }
}