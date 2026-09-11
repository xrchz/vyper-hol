stored: uint256

@external
def foo() -> uint256:
    self.stored = 5
    return self.stored
