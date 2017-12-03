#include "../test.cpp"

int main()
{
    return test("(quote (testing 1 (2.0) -3.14e159))", "(testing 1 (2.0) -3.14e159)");
}
