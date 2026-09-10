#pragma version 0.5.0a3

import manager

@external
@view
def read(addr: address) -> uint256:
    record: manager.Record = staticcall manager(addr).get_record()
    return record.value
