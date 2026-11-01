def factorial(n, end):
    if n == end:
        return 1
    return n * factorial(n + 1, end)


if __name__ == "__main__":
    print(factorial(1, 401))
