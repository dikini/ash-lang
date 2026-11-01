def range_list(n, end):
    if n == end:
        return None
    return (n, range_list(n + 1, end))


def map_list(f, values):
    if values is None:
        return None
    value, rest = values
    return (f(value), map_list(f, rest))


def fold(f, total, values):
    if values is None:
        return total
    value, rest = values
    return fold(f, f(total, value), rest)


def main():
    values = range_list(1, 401)
    transform = lambda value: value * value + 3 * value + 7
    transformed = map_list(transform, values)
    add = lambda total, value: total + value
    return fold(add, 0, transformed)


if __name__ == "__main__":
    print(main())
