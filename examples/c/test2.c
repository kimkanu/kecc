int g_int = -1;            // global variable
int main() {              // function
    int l_int = g_int;        // local variable
    if (l_int == 1) {
        return 3;
    }
    return g_int + l_int;
}
