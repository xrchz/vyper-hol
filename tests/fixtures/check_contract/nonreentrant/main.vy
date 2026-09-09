count: uint256

@external
@nonreentrant
def increment():
    self.count += 1
