"""Small delivered-byte fixtures; cryptographic eligibility is checked separately in Lean."""


def manifest():
    return {
        'schemaVersion': 1,
        'sizes': {'trapdoor': 16, 'proof': 64},
        'layout': {'message': 4096, 'commitment': 2**32 + 4096,
                   'trapdoor': 2**32 + 4128, 'indices': 2**32 + 4144,
                   'values': 2**32 + 4144 + 2**27, 'proof': 2**33 + 4144 + 2**27},
        'steps': {'commit': 20, 'opening': 20, 'check': 20},
        'images': {name: {'code': '73000000', 'data': ''}
                   for name in ('commit', 'opening', 'check')},
    }
