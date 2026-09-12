stored: uint256

@deploy
def __init__():
    self.stored = 5

@external
def foo() -> uint256:
    return self.stored
