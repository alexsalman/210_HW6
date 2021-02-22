datatype Tree<T> = Leaf | Node(Tree<T>, Tree<T>, T)
datatype List<T> = Nil | Cons(T, List<T>)

function flatten<T>(tree:Tree<T>):List<T>
{
    match tree
    case Leaf => Nil
    case Node (left, right, e) => append (flatten (left), Cons  (e, flatten (right)))
}

function append<T>(xs:List<T>, ys:List<T>):List<T>
    ensures len(append(xs,ys)) == len(xs) + len(ys);
    ensures xs == Nil ==> append(xs, ys) == ys
    ensures ys == Nil ==> append(xs, ys) == xs
{
	match(xs)
    case Nil => ys
    case Cons(x, xs') => Cons(x, append(xs', ys))
}

function treeContains<T>(tree:Tree<T>, element:T):bool
{
	match tree
}

function listContains<T>(xs:List<T>, element:T):bool
{
	
}


lemma sameElements<T>(tree:Tree<T>, element:T)
ensures treeContains(tree, element) <==> listContains(flatten(tree), element)
{
	// True => True
    // False => False
    // True x False
    // False x True
}