//completed and submitted on 3/1/2021
//alex salman aalsalma@ucsc.edu

datatype Tree<T> = Leaf | Node(Tree<T>, Tree<T>, T)
datatype List<T> = Nil | Cons(T, List<T>)

function flatten<T>(tree:Tree<T>):List<T>
decreases tree
{
    match tree
    case Leaf => Nil
    case Node(left, right, t) => Cons(t, append(flatten(left), flatten(right)))
}

function append<T>(xs:List<T>, ys:List<T>):List<T>
decreases xs
{
    match(xs)
    case Nil => ys
    case Cons(x, xs') => Cons(x, append(xs', ys))
}

function treeContains<T>(tree:Tree<T>, element:T):bool
decreases tree
{
	match tree
    case Leaf => false
    case Node(left, right, t) => t == element || treeContains(left, element) || treeContains(right, element)
}

function listContains<T>(xs:List<T>, element:T):bool
decreases xs
{
	match xs
    case Nil => false
    case Cons(t, xs') => t == element || listContains(xs', element)
}

lemma memberAppend<T>(x:T,ys:List<T>,zs:List<T>)
decreases ys
decreases zs
ensures listContains(append(ys,zs), x) == (listContains(ys, x) || listContains(zs, x))
{
    match ys
    case Nil => {}
    case Cons(y,ys') => {
        memberAppend(x,ys',zs);
        assert listContains(append(ys',zs),x) == (listContains(ys',x) || listContains(zs,x));
        assert listContains(append(ys,zs),x)
            == listContains(append(Cons(y,ys'),zs),x)
            == listContains(Cons(y,append(ys',zs)),x)
            == (x==y || listContains((append(ys',zs)),x))
            == (x==y || listContains(ys',x) || listContains(zs,x))
            == (listContains(Cons(y,ys'),x) || listContains(zs,x))
            == (listContains(ys,x)          || listContains(zs,x))
            ;
    }
}

lemma sameElements<T>(tree:Tree<T>, element:T)
decreases tree
ensures treeContains(tree, element) <==> listContains(flatten(tree), element)
{ 
    match tree
    case Leaf => {}
    case Node(left, right, t) => {
        sameElements(left, element);
        sameElements(right, element);
        memberAppend(element,flatten(left),flatten(right));
        assert treeContains(Node(left, right, t), element)
            == (treeContains(left, element) || treeContains(right, element) || t == element)
            == (listContains(flatten(left), element) || listContains(flatten(right), element) || t == element)
            == (listContains(append(flatten(left),flatten(right)), element) || t == element)
            == listContains (Cons(t, append(flatten(left),flatten(right))), element)
            == listContains(flatten(Node(left, right, t)), element)
            ;
    }
}