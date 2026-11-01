def fibonacci(n, end):
    if n == end:
        return 0
    if n + 1 == end:
        return 1
    return fibonacci(n + 1, end) + fibonacci(n + 2, end)


if __name__ == "__main__":
    print(fibonacci(0, 22))
