int (fibonacci)(int n) {
    return n < 2 ? n : fibonacci(n - 2) + fibonacci(n - 1);
}

int main() {
    return fibonacci(9) == 34;
}
