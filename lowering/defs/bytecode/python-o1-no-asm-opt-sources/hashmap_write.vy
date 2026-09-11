stored: HashMap[uint256, uint256]

@external
def foo(k: uint256) -> uint256:
    self.stored[k] = 5
    return self.stored[k]
