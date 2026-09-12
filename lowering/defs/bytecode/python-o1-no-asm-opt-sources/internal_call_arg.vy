@internal
def bar(y: uint256) -> uint256:
    return y + 1

@external
def foo(x: uint256) -> uint256:
    return self.bar(x)
