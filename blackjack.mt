import "unittest" =~ [=> unittest]
import "lib/enum" =~ [=> makeEnum :DeepFrozen]
exports (makeBlackjack, makeDeck)

def id(x) as DeepFrozen:
    "The identity function with one argument."
    return x

# The colors of nodes.
def [Color :DeepFrozen,
     red :DeepFrozen,
     black :DeepFrozen] := makeEnum(["red", "black"])

# Store nodes as a nested list: [value, left, right, color]. Null nodes are
# stored as literal refs to null.

def size(node) as DeepFrozen:
    "The size of the node.

     This function costs O(n) time."

    def s := if (node =~ [_, left, right, _]) {
        1 + size(left) + size(right)
    } else { 0 }
    return s

def find(node, value, keyFn, ej) as DeepFrozen:
    "Find a value `v` in `node` such that `keyFn(value) <=> v`.

     This function costs O(n) time."

    return if (node =~ [v, left, right, _]):
        def comparison := keyFn(v).op__cmp(keyFn(value))
        if (comparison.isZero()):
            v
        else if (comparison.aboveZero()):
            find(left, value, keyFn, ej)
        else if (comparison.belowZero()):
            find(right, value, keyFn, ej)
        else:
            throw.eject(ej, `$value not comparable to $v`)
    else:
        throw.eject(ej, `$value not in tree`)

def rotateLeft([value, left, right, color]) as DeepFrozen:
    "Rotate the node left."

    def [rightValue, rightLeft, rightRight, _] := right
    def new := [value, left, rightLeft, red]
    return [rightValue, new, rightRight, color]

def rotateRight([value, left, right, color]) as DeepFrozen:
    "Rotate the node right."

    def [leftValue, leftLeft, leftRight, _] := left
    def new := [value, leftRight, right, red]
    return [leftValue, leftLeft, new, color]

def flip(node) as DeepFrozen:
    "Invert the colors of a node."

    return if (node =~ [value, left, right, color]):
        [value, flip(left), flip(right),
         (color == red).pick(black, red)]
    else:
        node

def balance(var node) as DeepFrozen:
    "Restore balance to the node."

    # First, lean left.
    if (node =~ [_, _, [_, _, _, ==red], _]):
        node := rotateLeft(node)

    # Prevent red parents from having red children on the left.
    if (node =~ [_, [_, [_, _, _, ==red], _, ==red], _, _]):
        node := rotateRight(node)

    # Finally, if both children are red, move the redness up one level.
    if (node =~ [_, [_, _, _, ==red], [_, _, _, ==red], _]):
        node := flip(node)

    return node

def testBalanceRight(assert):
    def node := [1, null, [2, null, null, red], black]
    def balanced := [2, [1, null, null, red], null, black]
    assert.equal(balance(node), balanced)

def testBalanceFour(assert):
    def node := [2, [1, null, null, red], [3, null, null, red], black]
    def balanced := [2, [1, null, null, black], [3, null, null, black], red]
    assert.equal(balance(node), balanced)

def testBalanceLeftFour(assert):
    def node := [3, [2, [1, null, null, red], null, red], null, black]
    def balanced := [2, [1, null, null, black], [3, null, null, black], red]
    assert.equal(balance(node), balanced)

unittest([
    testBalanceRight,
    testBalanceFour,
    testBalanceLeftFour,
])

def insert(node, value, keyFn, ej) as DeepFrozen:
    "Insert or update `value` with key `keyFn(value)` into this node.
    
     Balancing is done afterwards to repair the invariants."

    return if (node =~ [v, left, right, color]):
        def comparison := keyFn(v).op__cmp(keyFn(value))
        def [newNode, insertion] := if (comparison.isZero()) {
            [[value, left, right, color], false]
        } else if (comparison.aboveZero()) {
            def [newLeft, i] := insert(left, value, keyFn, ej)
            [[v, newLeft, right, color], i]
        } else if (comparison.belowZero()) {
            def [newRight, i] := insert(right, value, keyFn, ej)
            [[v, left, newRight, color], i]
        } else {
            throw.eject(ej, `$value not comparable to $v`)
        }
        [balance(newNode), insertion]
    else:
        return [[value, null, null, red], true]

def testInsertLeft(assert):
    def before := [0, null, null, red]
    def after := [-1, null, [0, null, null, black], red]
    assert.equal(insert(before, -1, id, null)[0], after)

def testInsertRight(assert):
    def before := [0, null, null, red]
    def after := [1, [0, null, null, black], null, red]
    assert.equal(insert(before, 1, id, null)[0], after)

unittest([
    # broken testInsertLeft,
    # broken testInsertRight,
])

def moveRedLeft(var node) as DeepFrozen:
    "Move red to the left."

    node := flip(node)
    if (node =~ [value, left, right, color] &&
        right =~ [_, [_, _, _, ==red], _, _]):
        node := [value, left, right.rotateRight(), color]
        node := rotateLeft(node)
        node := flip(node)

    return node

def moveRedRight(var node) as DeepFrozen:
    "Move red to the right."

    node := flip(node)
    if (node =~ [value, left, right, color] &&
        left =~ [_, [_, _, _, ==red], _, _]):
        node := rotateRight(node)
        node := flip(node)

    return node

def deleteMin(var node) as DeepFrozen:
    "Delete the left-most value."

    # Did we reach the bottom?
    if (node =~ [value, ==null, _, _]):
        return [null, value]

    # If we are out of reds on the left, then move some more reds left.
    if (node =~ [_, [_, [_, _, _, ==black], _, ==black], _, _]):
        node := moveRedLeft(node)

    # Recurse on the left.
    def [value, left, right, color] := node
    def [newLeft, returnValue] := deleteMin(left)
    node := [value, newLeft, right, color]

    return [balance(node), returnValue]

def deleteMax(var node) as DeepFrozen:
    "Delete the right-most value."

    # Reds normally lean to the left; try pulling one to the right.
    if (node =~ [_, [_, _, _, ==red], _, _]):
        node := rotateRight(node)

    # Did we reach the top?
    if (node =~ [value, _, ==null, _]):
        return [null, value]

    # If we're out of reds on the right, then get some more.
    if (node =~ [_, _, [_, [_, _, _, ==black], _, ==black], _]):
        node := moveRedRight(node)

    # Recurse on the right.
    def [value, left, right, color] := node
    def [newRight, returnValue] := deleteMax(node)
    node := [value, left, newRight, color]

    return [balance(node), returnValue]

def delete(var node, value, keyFn, ej) as DeepFrozen:
    "Delete a value from a node."

    # Guess we don't have it.
    if (node == null):
        throw.eject(ej, `$value not in tree`)

    def [v, _, _, _] := node
    def comparison := keyFn(v).op__cmp(keyFn(value))
    if (comparison.aboveZero()):
        # Ensure that there's sufficient red on the left.
        if (node =~ [_, [_, [_, _, _, ==black], _, ==black], _, _]):
            node := moveRedLeft(node)
        def [_, left, right, color] := node
        # Recurse to the left.
        node := [v, delete(left, value, keyFn, ej), right, color]
    else if (comparison.atMostZero()):
        # Lean to the right, if we were already leaning to the left.
        if (node =~ [_, [_, _, _, ==red], _, _]):
            node := rotateRight(node)

        # I don't really buy the original explanation right now, but
        # supposedly this is the best case.
        if (comparison.isZero() && node =~ [_, _, ==null, _]):
            return null

        # Do we need more reds on the right before we can traverse further?
        if (node =~ [_, _, [_, [_, _, _, ==black], _, ==black], _]):
            node := moveRedRight(node)

        if (comparison.belowZero()):
            # Recurse to the right.
            def [_, left, right, color] := node
            node := [v, left, delete(right, value, keyFn, ej), color]
        else:
            # We are the node to delete, so delete the stuff next to us and
            # use that value as our own.
            def [_, left, right, color] := node
            def [newRight, newValue] := deleteMin(right)
            node := [newValue, left, newRight, color]
    else:
        throw.eject(ej, `$value not comparable to $v`)

    return balance(node)

object makeBlackjack as DeepFrozen:
    "Maker of `DeepFrozen` immutable blackjacks."

    to fromIterable(iterable, => keyFn := id):
        var node := null
        for v in (iterable):
            def [newNode, _] := insert(node, v, keyFn, throw.eject)
            node := newNode
        return makeBlackjack(node, => keyFn)

    to run(node :DeepFrozen, => keyFn :DeepFrozen := id):
        return object blackjack as DeepFrozen:
            "A red-black tree.
            
            This object responds to the same methods as sets."

            to _printOn(out):
                out.print(`🂫 (${blackjack.asList()})`)

            to contains(value):
                return escape ej:
                    find(node, value, keyFn, ej)
                    true
                catch _:
                    false

            to size():
                return size(node)

            to _makeIterator():
                var i :Int := 0
                def stack := [].diverge()
                var currentNode := node

                return object bjIterator:
                    to next(ej):
                        while (currentNode != null):
                            stack.push(currentNode)
                            def [_, left, _, _] := currentNode
                            currentNode := left
                        if (stack.size() != 0):
                            currentNode := stack.pop()
                            def [value, _, right, _] := currentNode
                            def rv := [i, value]
                            i += 1
                            currentNode := right
                            return rv
                        else:
                            throw.eject(ej, "Iterator exhausted")

            to with(value):
                def [newNode, _] := insert(node, value, keyFn, throw.eject)
                return makeBlackjack(newNode, => keyFn)

            to without(value):
                return escape ej:
                    def newNode := delete(node, value, keyFn, ej)
                    return makeBlackjack(newNode, => keyFn)
                catch _:
                    blackjack

            to find(value):
                return find(node, value, keyFn)

            to extractMaximum():
                def [newNode, value] := deleteMax(node)
                return makeBlackjack(newNode, => keyFn)

            to extractMinimum():
                def [newNode, value] := deleteMin(node)
                return makeBlackjack(newNode, => keyFn)

            to asList():
                return _makeList.fromIterable(blackjack)

def testBJSize(assert):
    for i in (0..10):
        def bj := makeBlackjack.fromIterable(0..i)
        assert.equal(bj.size(), i + 1)

def testBJWith(assert):
    var bj := makeBlackjack(null)
    for i in (0..10):
        assert.equal(bj.contains(i), false)
        bj with= (i)
        assert.equal(bj.contains(i), true)

def testBJWithDuplicates(assert):
    var bj := makeBlackjack.fromIterable(0..10)
    for i in (0..10):
        bj with= (i)
        assert.equal(bj.size(), 11)

def testBJDiscardSize(assert):
    var bj := makeBlackjack.fromIterable(0..10)
    for i in (0..10):
        bj without= (i)
        assert.equal(bj.size(), 10 - i)

def testBJContains(assert):
    var bj := makeBlackjack.fromIterable(0..10)
    for i in (0..10):
        assert.equal(bj.contains(i), true)

unittest([
    testBJSize,
    testBJWith,
    testBJWithDuplicates,
    testBJDiscardSize,
    testBJContains,
])


def makeDeck(node :DeepFrozen, => keyFn :DeepFrozen := id) as DeepFrozen:
    def getter([k, v]) as DeepFrozen:
        return keyFn(k)

    return object deck as DeepFrozen:
        "A red-black tree.
        
        This object responds to the same methods as maps."

        to _printOn(out):
            out.print(`🂫 (${deck.asMap()})`)

        to size():
            return size(node)

        to _makeIterator():
            def stack := [].diverge()
            var currentNode := node

            return object deckIterator:
                to next(ej):
                    while (currentNode != null):
                        stack.push(currentNode)
                        def [_, left, _, _] := currentNode
                        currentNode := left
                    if (stack.size() != 0):
                        currentNode := stack.pop()
                        def [rv, _, right, _] := currentNode
                        currentNode := right
                        return rv
                    else:
                        throw.eject(ej, "Iterator exhausted")

        to get(key):
            return find(node, [key, null], getter, throw.eject)

        to fetch(key, thunk):
            return find(node, [key, null], getter, fn _ {thunk()})

        to with(key, value):
            def [newNode, _] := insert(node, [key, value], getter, throw.eject)
            return makeDeck(newNode)

        to without(key):
            def newNode := escape ej {
                delete(node, [key, null], getter, ej)
            } catch _ { node }
            return makeDeck(newNode)

        to asMap():
            var m := [].asMap()
            for k => v in (deck):
                m with= (k, v)
            return m
