@internal
def bar() -> uint256:
    return 7

@external
def foo() -> uint256:
    return self.bar()
