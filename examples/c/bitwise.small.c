int main() {
    unsigned char a = -1;
    unsigned char b = -128;
    unsigned char d = b | a; // -1 (255)
    unsigned char e = b & a; // -128 (128)
    
    return d == 255 && e == 128;
}
