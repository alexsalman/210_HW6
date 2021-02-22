datatype Tree<T> = Leaf | Node(Tree<T>, Tree<T>, T)
datatype List<T> = Nil | Cons(T, List<T>)

function flatten<T>(tree:Tree<T>):List<T>
{
    match Tree
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
    ensures element 
{
	match tree
    case Leaf => Nil

}
// Note that dafny doesn't quite understand that a == b is the same thing as a <==> b when they are booleans.
function listContains<T>(xs:List<T>, element:T):bool
{
	match xs
    case Nil => false
    case t == xs || List
}


lemma sameElements<T>(tree:Tree<T>, element:T)
ensures treeContains(tree, element) <==> listContains(flatten(tree), element)
{
	// True => True
    // False => False
    // True x False
    // False x True
}