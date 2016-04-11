import "unittest" =~ [=> unittest]
import "lib/enum" =~ [=> makeEnum :DeepFrozen]
exports ()

# The colors of nodes.
def [Color :DeepFrozen,
     red :DeepFrozen,
     black :DeepFrozen] := makeEnum(["red", "black"])

# Store nodes as a nested list: [value, left, right, color]. Null nodes are
# stored as literal refs to null.

def size(node) as DeepFrozen:
    "The size of the node.

     This function costs O(n) time."

    return if (node =~ [_, left, right, _]):
        1 + size(left) + size(right)
    else:
        0

def find(node, value, keyFn, ej) as DeepFrozen:
    "Find a value `v` in `node` such that `keyFn(value) <=> v`.

     This function costs O(n) time."

    return if (node =~ [v, left, right, _]):
        def comparison := keyFn(v).op__cmp(keyFn(value))
        if (comparison.isZero()):
            v
        else if (comparison.lessThanZero()):
            find(left, value, keyFn, ej)
        else if (comparison.greaterThanZero()):
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

def insert(node, value, keyFn, ej):
    "Insert or update `value` with key `keyFn(value)` into this node.
    
     Balancing is done afterwards to repair the invariants."

    return if (node =~ [v, left, right, color]):
        def comparison := keyFn(v).op__cmp(keyFn(value))
        def [newNode, insertion] := if (comparison.isZero()) {
            [[value, left, right, color], false]
        } else if (comparison.lessThanZero()) {
            def [newLeft, i] := insert(left, value, keyFn, ej)
            [[value, newLeft, right, color], i]
        } else if (comparison.greaterThanZero()) {
            def [newRight, i] := insert(right, value, keyFn, ej)
            [[value, left, newRight, color], i]
        } else {
            throw.eject(ej, `$value not comparable to $v`)
        }
        [balance(newNode), insertion]
    else:
        return [[value, null, null, red], true]

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
    if (comparison.lessThanZero()):
        # Ensure that there's sufficient red on the left.
        if (node =~ [_, [_, [_, _, _, ==black], _, ==black], _, _]):
            node := moveRedLeft(node)
        def [_, left, right, color] := node
        # Recurse to the left.
        node := [v, delete(left, value, keyFn, ej), right, color]
    else:
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

        if (comparison.greaterThanZero()):
            # Recurse to the right.
            def [_, left, right, color] := node
            node := [v, left, delete(right, value, keyFn, ej), color]
        else:
            # We are the node to delete, so delete the stuff next to us and
            # use that value as our own.
            def [_, left, right, color] := node
            def [newRight, newValue] := deleteMin(right)
            node := [newValue, left, newRight, color]

    return balance(node)
