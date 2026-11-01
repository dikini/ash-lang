def append(left, right):
    if left is None:
        return right
    value, rest = left
    return (value, append(rest, right))


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
    pair = (True, (False, None))
    four = append(pair, pair)
    eight = append(four, four)
    sixteen = append(eight, eight)
    thirty_two = append(sixteen, sixteen)
    sixty_four = append(thirty_two, thirty_two)
    one_twenty_eight = append(sixty_four, sixty_four)
    two_fifty_six = append(one_twenty_eight, one_twenty_eight)
    tail = append(one_twenty_eight, sixteen)
    values = append(two_fifty_six, tail)

    def flip(value):
        if value:
            return False
        return True

    transformed = map_list(flip, values)

    def xor(total, value):
        if not value:
            return total
        if total:
            return False
        return True

    return fold(xor, False, transformed)


if __name__ == "__main__":
    print("true" if main() else "false")
