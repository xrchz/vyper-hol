@external
def choose(x: uint256 = 7) -> uint256:
    total: uint256 = 0
    for i: uint256 in range(3):
        total += i
    if x > total:
        return x
    return total
