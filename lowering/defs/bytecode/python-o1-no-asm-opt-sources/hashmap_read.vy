stored: HashMap[uint256, uint256]

@external
def foo(k: uint256) -> uint256:
    return self.stored[k]
