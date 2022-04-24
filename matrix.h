#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <array>

using std::vector;
using std::cout;
using std::cin;
using std::array;

class BigInteger;

class Rational;

BigInteger operator/(const BigInteger& a, const BigInteger& b);

BigInteger operator*(const BigInteger& a, const BigInteger& b);

BigInteger operator%(const BigInteger& a, const BigInteger& b);

std::ostream& operator<<(std::ostream& out, const BigInteger& s);

class BigInteger {
private:
    std::vector<int> bigint = {0};
    bool isPositiveOrZero = true;
    static constexpr long long mod = 998244353;
    static const long long WN = 31;
    static const long long invertWN = 128805723;
    static const int logmax = 1;
    static const int max = 10;

    static long long binpow(long long a, long long n) {
        a %= mod;
        if (n == 0) return 1;
        if (n % 2 == 1) {
            return (binpow(a, n - 1) * a) % mod;
        } else {
            long long b = binpow(a, n / 2);
            return (b * b) % mod;
        }
    }

    static size_t reverse(size_t k, size_t n) {
        size_t ans = 0;
        while (n > 1) {
            n /= 2;
            ans += n * (k % 2);
            k /= 2;
        }
        return ans;
    }

    static void fft(vector<int>& a, size_t n, long long wn) {
        wn %= mod;
        for (size_t i = 0; i < n; ++i) {
            if (i < reverse(i, n)) {
                std::swap(a[i], a[reverse(i, n)]);
            }
        }
        for (size_t l = 2; l <= n; l *= 2) {
            long long wl = wn;
            for (size_t i = l; i < n; i *= 2) {
                wl = wl * wl;
                wl %= mod;
            }
            for (size_t st = 0; st < n; st += l) {
                long long deg = 1;
                for (size_t j = 0; j < l / 2; ++j) {
                    long long u = a[st + j] % mod;
                    long long v = (deg * static_cast<long long>(a[st + j + l / 2])) % mod;
                    a[st + j] = u + v;
                    a[st + j + l / 2] = u - v;
                    a[st + j + l / 2] %= mod;
                    if (a[st + j + l / 2] < 0) {
                        a[st + j + l / 2] += mod;
                    }
                    a[st + j] %= mod;

                    if (a[st + j] < 0) {
                        a[st + j] += mod;
                    }
                    deg *= wl;
                    deg %= mod;
                }
            }
        }
    }

    bool isZero() const {
        return (bigint.size() == 1 && bigint[0] == 0);
    }

    bool isRightAbsLess(const BigInteger& a) const {
        if (bigint.size() < a.bigint.size()) {
            return false;
        }
        if (a.bigint.size() < bigint.size()) {
            return true;
        }
        for (size_t i = bigint.size() - 1;; --i) {
            if (bigint[i] < a.bigint[i]) {
                return false;
            }
            if (bigint[i] > a.bigint[i]) {
                return true;
            }
            if (i == 0) break;
        }
        return false;
    }

    void sizeNormalize() {
        while (bigint.size() > 1 && bigint.back() == 0) {
            bigint.pop_back();
        }
        if (isZero()) {
            isPositiveOrZero = true;
        }
    }

    void normalize(bool toPositive) {
        if (toPositive) {
            for (size_t i = 0; i < bigint.size(); ++i) {
                if (bigint.size() == i + 1 && bigint[i] >= max) {
                    bigint.push_back(0);
                }
                if (bigint[i] >= max) {
                    bigint[i + 1] += bigint[i] / max;
                    bigint[i] %= max;
                }
                if (bigint[i] < 0) {
                    bigint[i + 1] += (bigint[i] - max + 1) / max;
                    bigint[i] = ((bigint[i] % max) + max) % max;
                }

            }
            sizeNormalize();
            return;
        }
        for (size_t i = 0; i < bigint.size(); ++i) {
            if (bigint[i] > 0) {
                bigint[i] -= max;
                ++bigint[i + 1];
            }
            bigint[i] = abs(bigint[i]);

        }
        sizeNormalize();
    }

public:

    void addZeros(int zeroAmount) {
        int newSize = bigint.size();
        newSize += zeroAmount;
        vector<int> newBigint(newSize);
        for (size_t i = zeroAmount; i < bigint.size() + zeroAmount; ++i) {
            newBigint[i] = bigint[i - zeroAmount];
        }
        bigint = newBigint;
    }

    BigInteger() = default;

    BigInteger(int a) {

        if (a != 0) {
            bigint = {};
        };
        if (a < 0) {
            a *= -1;
            isPositiveOrZero = false;
        }

        while (a > 0) {
            int c = a % max;
            bigint.push_back(c);
            a /= max;
        }
    }

    BigInteger operator-() const {
        BigInteger copy = *this;
        copy.isPositiveOrZero = !isPositiveOrZero;
        if (copy.isZero()) copy.isPositiveOrZero = true;
        return copy;
    }

    BigInteger& operator+=(const BigInteger& summand)& {
        if (summand.isPositiveOrZero == isPositiveOrZero) {
            bigint.reserve(summand.bigint.size());
            for (size_t i = 0; i < summand.bigint.size(); ++i) {
                if (i >= bigint.size()) {
                    bigint.push_back(0);
                }
                bigint[i] += summand.bigint[i];
            }

            normalize(true);
            if (isZero()) isPositiveOrZero = true;
            return *this;
        }
        if (isRightAbsLess(summand)) {
            for (size_t i = 0; i < summand.bigint.size(); ++i) {
                bigint[i] -= summand.bigint[i];
            }
            normalize(true);
            if (isZero()) {
                isPositiveOrZero = true;
            }
            return *this;
        }
        for (size_t i = 0; i < summand.bigint.size(); ++i) {
            if (i == bigint.size()) {
                bigint.push_back(0);
            }
            bigint[i] -= summand.bigint[i];
        }
        normalize(false);
        isPositiveOrZero = summand.isPositiveOrZero;
        if (isZero()) {
            isPositiveOrZero = true;
        }
        return *this;
    }

    BigInteger& operator-=(const BigInteger& deductible)& {
        *this += -deductible;
        return *this;
    }

    BigInteger& operator++() {
        *this += 1;
        return *this;
    }

    BigInteger& operator--() {
        *this -= 1;
        return *this;
    }

    BigInteger operator++(int) {
        BigInteger copy = *this;
        *this += 1;
        return copy;
    }

    BigInteger operator--(int) {
        BigInteger copy = *this;
        *this -= 1;
        return copy;
    }

    explicit operator bool() const {
        return !isZero();
    }

    std::string toString() const {
        std::string ans;
        ans.reserve(bigint.size());
        for (size_t i = 0; i < bigint.size(); ++i) {
            int copy = bigint[i];
            for (int j = 0; j < logmax; ++j) {
                if (copy == 0 && i + 1 == bigint.size()) {
                    break;
                }
                ans += static_cast<char>(copy % 10 + 48);
                copy /= 10;
            }
        }
        if (isPositiveOrZero == 0) {
            ans += '-';
        }
        std::reverse(ans.begin(), ans.end());
        if (ans.empty() || ans == "-") {
            ans = "0";
        }
        return ans;
    }

    friend std::istream& operator>>(std::istream& in, BigInteger& a);

    BigInteger& operator*=(const BigInteger& multiplier)& {
        if (bigint.size() < 2000 || multiplier.bigint.size() < 2000) {
            vector<int> copy = bigint;
            int newSize = static_cast<int>(bigint.size()) + static_cast<int>(multiplier.bigint.size());
            bigint.resize(newSize);
            for (int i = static_cast<int>(bigint.size()) - 1; i > -1; --i) {
                for (int j = static_cast<int>(multiplier.bigint.size()) - 1; j > -1; --j) {
                    if (j == 0) {
                        bigint[i + j] = bigint[i] * multiplier.bigint[j];
                        continue;
                    }
                    bigint[i + j] += bigint[i] * multiplier.bigint[j];
                }
            }
            isPositiveOrZero ^= (1 - multiplier.isPositiveOrZero);
            normalize(true);
            if (isZero()) {
                isPositiveOrZero = true;
            }
            return *this;
        }
        vector<int> bigint2 = multiplier.bigint;
        long long wn = WN;
        long long invertwn = invertWN;
        isPositiveOrZero ^= (1 - multiplier.isPositiveOrZero);
        size_t n = 1;
        int st = 0;
        while (n < bigint.size() + multiplier.bigint.size()) {
            n *= 2;
            st++;
        }
        for (int i = 0; i < 23 - st; ++i) {
            wn *= wn;
            invertwn *= invertwn;
            wn %= mod;
            invertwn %= mod;
        }
        long long copywn = wn;
        bigint.resize(n);
        bigint2.resize(n);
        fft(bigint, n, wn);
        fft(bigint2, n, copywn);
        for (size_t i = 0; i < n; ++i) {
            long long c = (static_cast<long long>(bigint[i]) * static_cast<long long>(bigint2[i])) % mod;
            bigint[i] = c;
        }
        fft(bigint, n, invertwn);
        long long z = binpow(n, mod - 2);
        z %= mod;
        for (size_t i = 0; i < n; ++i) {
            long long c = (z * static_cast<long long>(bigint[i])) % mod;
            bigint[i] = c;
            if (bigint[i] < -mod / 2) {
                bigint[i] += mod;
            }
        }
        normalize(true);
        if (isZero()) {
            isPositiveOrZero = true;
        }
        return *this;
    }

    BigInteger& operator/=(const BigInteger& divider)& {
        if (divider.bigint.size() == 1 && divider.bigint[0] == 1) {
            if (divider.isPositiveOrZero) {
                return *this;
            }
            isPositiveOrZero ^= 1;
            return *this;
        }
        if (*this == divider) {
            BigInteger one;
            one.isPositiveOrZero = true;
            one.bigint.resize(1);
            one.bigint[0] = 1;
            operator=(one);
            *this = one;
            return *this;
        }
        BigInteger quotient;
        int size2 = 1;
        if (bigint.size() + 1 > divider.bigint.size()) {
            size2 = bigint.size() + 1 - divider.bigint.size();
        }
        quotient.bigint.resize(size2);
        bool realsignofthis = isPositiveOrZero;
        BigInteger copyDivider = divider;
        while (isRightAbsLess(divider)) {
            int degreeof10 = 0;
            if (bigint.size() > copyDivider.bigint.size() + 1) {
                degreeof10 = bigint.size() - copyDivider.bigint.size() - 1;
            }
            copyDivider.addZeros(degreeof10);
            BigInteger copyDivider2 = copyDivider * 5;
            if (isRightAbsLess(copyDivider2)) {
                if (divider.isPositiveOrZero == isPositiveOrZero) {
                    *this -= copyDivider2;
                } else {
                    *this += copyDivider2;
                }
                quotient.bigint[degreeof10] += 5;
            }
            while (isRightAbsLess(copyDivider)) {
                if (divider.isPositiveOrZero == isPositiveOrZero) {
                    *this -= copyDivider;
                } else {
                    *this += copyDivider;
                }
                ++quotient.bigint[degreeof10];
            }
            copyDivider = divider;
        }
        if (divider.bigint.size() == bigint.size()) {
            bool flag = false;
            for (size_t i = 0; i < bigint.size(); ++i) {
                if (bigint[i] != divider.bigint[i]) {
                    flag = true;
                    break;
                }
            }
            if (flag == 0) {
                ++quotient.bigint[0];
            }
        }
        quotient.normalize(true);
        quotient.isPositiveOrZero = divider.isPositiveOrZero ^ (1 - realsignofthis);
        if (quotient.isZero()) {
            quotient.isPositiveOrZero = true;
        }
        *this = quotient;
        return *this;
    }

    bool isEven() {
        return !(bigint[0] % 2);
    }

    void divideByTwo() {
        for (size_t i = bigint.size() - 1; i >= 1; --i) {
            if (i == 0) break;
            if (bigint[i] % 2 == 1) bigint[i - 1] += 10;
            bigint[i] /= 2;

            if (i == 1) break;
        }
        bigint[0] /= 2;
        normalize(true);
    }

    BigInteger& operator%=(const BigInteger& modul)& {
        BigInteger a;
        *this -= (*this / modul) * modul;
        return *this;
    }

    friend class Rational;

    friend bool operator==(const BigInteger& a, const BigInteger& b);

    friend bool operator>(const BigInteger& a, const BigInteger& b);

    friend std::istream& operator>>(std::istream& in, Rational& c);
};

bool operator==(const BigInteger& a, const BigInteger& b) {
    if (a.bigint.size() != b.bigint.size() || a.isPositiveOrZero != b.isPositiveOrZero) return false;
    for (size_t i = 0; i < a.bigint.size(); ++i) {
        if (a.bigint[i] != b.bigint[i]) {
            return false;
        }
    }
    return true;
}

bool operator>(const BigInteger& a, const BigInteger& b) {
    if (a == b) {
        return false;
    }
    if (a.isPositiveOrZero > b.isPositiveOrZero) return true;
    if (a.isPositiveOrZero < b.isPositiveOrZero) return false;
    return !a.isPositiveOrZero ^ a.isRightAbsLess(b);
}

bool operator<(const BigInteger& a, const BigInteger& b) {
    return (b > a);
}

bool operator<=(const BigInteger& a, const BigInteger& b) {
    return !(a > b);
}

bool operator>=(const BigInteger& a, const BigInteger& b) {
    return !(a < b);
}

bool operator!=(const BigInteger& a, const BigInteger& b) {
    return !(a == b);
}

BigInteger gcd(BigInteger& a, BigInteger& b) {
    if (a == 0) return b;
    if (b == 0) return a;
    if (a.isEven() && b.isEven()) {
        a.divideByTwo();
        b.divideByTwo();
        return gcd(a, b) * 2;
    }
    if (b.isEven()) {
        b.divideByTwo();
        return gcd(a, b);
    }
    if (a.isEven()) {
        a.divideByTwo();
        if (a >= b) return gcd(a, b);
        return gcd(b, a);
    }
    if (a < b) std::swap(a, b);
    a -= b;
    if (a >= b) return gcd(a, b);
    return gcd(b, a);
}

std::istream& operator>>(std::istream& in, BigInteger& a) {
    a.bigint.clear();
    std::string s;
    in >> s;
    int length = static_cast<int>(s.size());
    if (s[0] == '-') {
        a.isPositiveOrZero = false;
    } else {
        a.isPositiveOrZero = true;
    }
    a.bigint.resize((length + BigInteger::logmax - 1) / BigInteger::logmax);
    int whichint = 0;
    for (int i = length - 1;; i -= BigInteger::logmax) {
        int degree10 = 1;
        int currentInt = 0;
        for (int j = 0; j < BigInteger::logmax && i - j >= 0; ++j) {
            if (s[i - j] == '-' || s[i - j] == '+') {
                break;
            }
            currentInt += degree10 * (s[i - j] - 48);
            degree10 *= 10;
        }
        a.bigint[whichint] = currentInt;
        ++whichint;
        if (i < BigInteger::logmax) break;
    }
    if (a.isPositiveOrZero == 0) {
        a.bigint.pop_back();
    }
    if (a.bigint.size() == 1 && a.bigint[0] == 0) {
        a.isPositiveOrZero = true;
    }
    return in;
}

std::ostream& operator<<(std::ostream& out, const BigInteger& s) {
    out << s.toString();
    return out;
}

BigInteger operator+(const BigInteger& a, const BigInteger& b) {
    BigInteger copy = a;
    copy += b;
    return copy;
}

BigInteger operator-(const BigInteger& a, const BigInteger& b) {
    BigInteger copy = a;
    copy -= b;
    return copy;
}

BigInteger operator*(const BigInteger& a, const BigInteger& b) {
    BigInteger copy = a;
    copy *= b;
    return copy;
}

BigInteger operator/(const BigInteger& a, const BigInteger& b) {
    BigInteger copy = a;
    copy /= b;
    return copy;
}

BigInteger operator%(const BigInteger& a, const BigInteger& b) {
    BigInteger copy = a;
    copy %= b;
    return copy;
}

class Rational {
private:
    BigInteger numerator = BigInteger(0);
    BigInteger denominator = BigInteger(1);

    void divideByGcd() {
        BigInteger copyNumerator = numerator;
        BigInteger copyDenominator = denominator;
        copyNumerator.isPositiveOrZero = true;
        copyDenominator.isPositiveOrZero = true;
        BigInteger GCD = gcd(copyNumerator, copyDenominator);
        if (numerator.isPositiveOrZero == denominator.isPositiveOrZero) {
            numerator.isPositiveOrZero = true;
        } else {
            numerator.isPositiveOrZero = numerator.isZero();
        }
        denominator.isPositiveOrZero = true;
        numerator /= GCD;
        denominator /= GCD;
    }

public:
    Rational() = default;

    Rational(const BigInteger& a, const BigInteger& b) {
        numerator = a;
        denominator = b;
        if (denominator < 0) {
            numerator = -numerator;
            denominator = -denominator;
        }
        divideByGcd();
    }

    Rational(const BigInteger& a) {
        numerator = a;
        denominator = BigInteger(1);
    }

    Rational(int x) {
        numerator = BigInteger(x);
        denominator = 1;
    }

    Rational& operator+=(const Rational& summand)& {
        numerator = summand.denominator * numerator + summand.numerator * denominator;
        denominator *= summand.denominator;
        divideByGcd();
        return *this;
    }

    Rational& operator-=(const Rational& deductible)& {
        numerator = deductible.denominator * numerator - deductible.numerator * denominator;
        denominator *= deductible.denominator;
        divideByGcd();
        return *this;
    }

    Rational& operator*=(const Rational& multiplier)& {
        numerator *= multiplier.numerator;
        denominator *= multiplier.denominator;
        divideByGcd();
        return *this;
    }

    Rational& operator/=(const Rational& divider)& {
        if (this == &divider) {
            *this = 1;
            return *this;
        }
        numerator *= divider.denominator;
        denominator *= divider.numerator;
        divideByGcd();
        return *this;
    }

    Rational operator-() const {
        Rational copy = *this;
        if (numerator != 0) {
            copy.numerator = -numerator;
        }
        return copy;
    }

    std::string toString() {
        std::string ans = numerator.toString();
        if (denominator.bigint.size() != 1 || denominator.bigint[0] != 1) {
            ans += '/';
            ans += denominator.toString();
        }
        return ans;
    }

    std::string asDecimal(int precision = 0) const {
        BigInteger increasedNumerator = numerator;
        increasedNumerator.addZeros(precision);
        BigInteger left = increasedNumerator % denominator;
        increasedNumerator /= denominator;
        left.isPositiveOrZero = true;
        if (2 * left >= denominator) {
            ++increasedNumerator;
        }
        std::string ans;
        if (increasedNumerator < 0) {
            ans += '-';
        }
        if (static_cast<int>(increasedNumerator.bigint.size()) > precision) {
            for (size_t i = increasedNumerator.bigint.size() - 1;; i--) {
                ans += (static_cast<char>(increasedNumerator.bigint[i] + '0'));
                if (static_cast<int>(i) == precision) break;
            }
        }
        if ((ans.size() == 1 && ans[0] == '-') || ans.size() == 0) {
            ans += '0';
        }
        if (precision != 0) {
            ans += '.';
        }
        for (int i = precision - 1; i >= 0; i--) {
            if (i >= static_cast<int>(increasedNumerator.bigint.size())) {
                ans += '0';
                continue;
            }
            ans += (static_cast<char>(increasedNumerator.bigint[i] + '0'));
        }
        return ans;
    }

    explicit operator double() {
        return std::stod(asDecimal(18));
    }

    friend bool operator==(const Rational& a, const Rational& b);

    friend bool operator<(const Rational& a, const Rational& b);

    friend std::istream& operator>>(std::istream& in, Rational& c);
};

bool operator==(const Rational& a, const Rational& b) {
    return (a.numerator == b.numerator && a.denominator == b.denominator);
}

bool operator!=(const Rational& a, const Rational& b) {
    return !(a == b);
}

bool operator<(const Rational& a, const Rational& b) {
    return (a.numerator * b.denominator < b.numerator * a.denominator);
}

bool operator>(const Rational& a, const Rational& b) {
    return (b < a);
}

bool operator>=(const Rational& a, const Rational& b) {
    return !(b > a);
}

bool operator<=(const Rational& a, const Rational& b) {
    return !(b < a);
}

Rational operator+(const Rational& a, const Rational& b) {
    Rational copy = a;
    copy += b;
    return copy;
}

Rational operator-(const Rational& a, const Rational& b) {
    Rational copy = a;
    copy -= b;
    return copy;
}

Rational operator*(const Rational& a, const Rational& b) {
    Rational copy = a;
    copy *= b;
    return copy;
}

Rational operator/(const Rational& a, const Rational& b) {
    Rational copy = a;
    copy /= b;
    return copy;
}

std::istream& operator>>(std::istream& in, Rational& c) {
    c.numerator.bigint.clear();
    BigInteger a;
    std::string s;
    in >> s;
    int length = static_cast<int>(s.size());
    if (s[0] == '-') {
        a.isPositiveOrZero = false;
    } else {
        a.isPositiveOrZero = true;
    }
    a.bigint.resize((length + BigInteger::logmax - 1) / BigInteger::logmax);
    int whichint = 0;
    for (int i = length - 1; i > -1; i -= BigInteger::logmax) {
        int degree10 = 1;
        int currentInt = 0;
        for (int j = 0; j < BigInteger::logmax && i - j >= 0; ++j) {
            if (s[i - j] == '-' || s[i - j] == '+') {
                break;
            }
            currentInt += degree10 * (s[i - j] - 48);
            degree10 *= 10;
        }

        a.bigint[whichint] = currentInt;
        ++whichint;
    }
    if (a.isPositiveOrZero == 0) {
        a.bigint.pop_back();
    }
    if (a.isZero()) {
        a.isPositiveOrZero = true;
    }
    c.numerator = a;
    c.denominator.bigint[0] = 1;
    c.denominator.isPositiveOrZero = true;
    return in;
}

std::ostream& operator<<(std::ostream& out, const Rational& a) {
    out << a.asDecimal(18);
    return out;
}

long long binPow(long long a, int degree, long long mod) {
    a %= mod;
    if (degree == 1) return a;
    if (degree % 2 == 0) {
        return binPow(a * a, degree / 2, mod) % mod;
    }
    long long c = binPow(a * a, degree / 2, mod) % mod;
    c *= a;
    c %= mod;
    return c;
}

using std::vector;
template<int N, int K>
struct IsPrimeHelper {
    static const int newK = (K * K > N ? 0 : K + 1);
    static const bool value = N % K != 0 && IsPrimeHelper<N, newK>::value;
};
template<int N>
struct IsPrimeHelper<N, 0> {
    static const bool value = true;
};
template<int N>
struct IsPrime {
    static const bool value = IsPrimeHelper<N, 2>::value;
};

template<int N>
class Residue {
    static const bool isPrime = IsPrime<N>::value;
    int value = 0;
public:
    Residue() = default;

    explicit Residue(int x) {
        value = x % N;
        if (value < 0) value += N;
    }

    explicit operator int() const {
        return value;
    }

    Residue& operator+=(const Residue& summand)& {
        value += summand.value;
        if (value >= N) value -= N;
        return *this;
    }

    Residue& operator-=(const Residue& summand)& {
        value -= summand.value;
        if (value < 0) value += N;
        return *this;
    }

    Residue& operator*=(const Residue& summand)& {
        value *= summand.value;
        value %= N;
        return *this;
    }

    Residue& operator/=(const Residue& divider)& {
        static_assert(isPrime, "You can't divide by composite number!");
        value *= binPow(divider.value, N - 2, N);
        value %= N;
        if (value < 0) value += N;
        return *this;
    }

    bool operator==(const int x) const {
        return x == value;
    }

    bool operator!=(const int x) const {
        return x != value;
    }

    bool operator==(const Residue x) const {
        return x.value == value;
    }

    bool operator!=(const Residue x) const {
        return x.value != value;
    }
};

template<int N>
Residue<N> operator+(const Residue<N>& a, const Residue<N>& b) {
    Residue<N> copy = a;
    copy += b;
    return copy;
}

template<int N>
Residue<N> operator-(const Residue<N>& a, const Residue<N>& b) {
    Residue<N> copy = a;
    copy -= b;
    return copy;
}

template<int N>
Residue<N> operator*(const Residue<N>& a, const Residue<N>& b) {
    Residue<N> copy = a;
    copy *= b;
    return copy;
}

template<int N>
Residue<N> operator/(const Residue<N>& a, const Residue<N>& b) {
    Residue<N> copy = a;
    copy /= b;
    return copy;
}

template<int N>
std::ostream& operator<<(std::ostream& out, const Residue<N>& a) {
    out << int(a);
    return out;
}

template<size_t N, size_t M, typename Field = Rational>
class Matrix {
private:
    vector<array<Field, M>> matrix;

    Matrix helpforinvert() const {
        static_assert(N == M, "Matrix isn't square");
        vector<array<Field, 2 * M>> newmatrix(N, array<Field, 2 * M>());
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < N; ++j) {
                newmatrix[i][j] = matrix[i][j];
            }
        }
        for (size_t i = 0; i < N; ++i) {
            newmatrix[i][i + N] = Field(1);
        }
        Matrix<N, N + M, Field> copy(newmatrix);

        Matrix<N, N + M, Field> copy2 = copy.GaussTransformation();
        for (size_t i = 0; i < N; ++i) {
            Field x = copy2[i][i];
            for (size_t j = 0; j < 2 * N; ++j) {
                copy2[i][j] /= x;
            }
        }
        Matrix<N, N, Field> answer;
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < N; ++j) {
                answer[i][j] = copy2[i][j + N];
            }
        }
        return answer;
    }

public:
    Matrix() {
        matrix.resize(N, array<Field, M>());
        if (N == M) {
            for (size_t i = 0; i < N; ++i) {
                matrix[i][i] = static_cast<Field>(1);
            }
        }
    }

    Matrix(vector<vector<int>>& table) {
        matrix.resize(N, array<Field, M>());
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < M; ++j) {
                matrix[i][j] = static_cast<Field>(table[i][j]);
            }
        }
    }

    Matrix(vector<array<Field, M>>& table) {
        matrix.resize(N, array<Field, M>());
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < M; ++j) {
                matrix[i][j] = table[i][j];
            }
        }
    }

    Matrix(std::initializer_list<std::initializer_list<int>> table) {
        matrix.resize(N, array<Field, M>());
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < M; ++j) {
                matrix[i][j] = Field(*((table.begin() + i)->begin() + j));
            }
        }
    }

    Matrix& operator+=(const Matrix<N, M, Field>& summand)& {
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < M; ++j) {
                matrix[i][j] += summand.matrix[i][j];
            }
        }
        return *this;
    }

    Matrix& operator-=(const Matrix<N, M, Field>& summand)& {
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < M; ++j) {
                matrix[i][j] -= summand.matrix[i][j];
            }
        }
        return *this;
    }

    bool operator==(const Matrix<N, M, Field>& compared) const {
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < M; ++j) {
                if (matrix[i][j] != compared.matrix[i][j]) return false;
            }
        }
        return true;
    }

    bool operator!=(const Matrix& compared) const {
        return !(*this == compared);
    }

    array<Field, M>& operator[](size_t i) {
        return matrix[i];
    }

    const array<Field, M>& operator[](size_t i) const {
        return matrix[i];
    }

    Matrix& operator*=(Field multiplier)& {
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < M; ++j) {
                matrix[i][j] *= multiplier;
            }
        }
        return *this;
    }

    Matrix operator*(Field multiplier) const {
        Matrix copy = *this;
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < M; ++j) {
                copy.matrix[i][j] *= multiplier;
            }
        }
        return *this;
    }

    Matrix& operator*=(const Matrix<N, M, Field>& multiplier)& {
        static_assert(N == M, "Matrix isn't square");
        Matrix<N, N, Field> result;
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < N; ++j) {
                result[i][j] = static_cast<Field>(0);
                for (size_t q = 0; q < N; ++q) {
                    result[i][j] += matrix[i][q] * multiplier[q][j];
                }
            }
        }
        *this = result;
        return *this;
    }

    Matrix GaussTransformation() const {
        Matrix copy = *this;
        size_t min = 0;
        for (size_t j = 0; j < M; ++j) {
            bool flag = false;
            for (size_t i = min; i < N; ++i) {
                if (copy.matrix[i][j] == 0) continue;
                if (i != min) {
                    std::swap(copy.matrix[i], copy.matrix[min]);
                }
                for (size_t q = 0; q < N; ++q) {
                    if (q == min) continue;
                    Field z = copy.matrix[q][j] / copy.matrix[min][j];
                    for (size_t w = 0; w < M; w++) {
                        copy.matrix[q][w] -= copy.matrix[min][w] * z;
                    }
                }
                flag = true;
                break;
            }
            if (flag) min++;
        }
        return copy;
    }

    Field det() const {
        static_assert(N == M, "Matrix isn't square");
        Matrix copy = GaussTransformation();
        Field ans = Field(1);
        for (size_t i = 0; i < N; ++i) {
            ans *= copy.matrix[i][i];
        }
        return ans;
    }

    int rank() const {
        Matrix copy = GaussTransformation();
        int ans = 0;
        for (size_t i = 0; i < N; ++i) {
            bool areOnlyZeroes = true;
            for (size_t j = 0; j < M; ++j) {
                if (copy.matrix[i][j] != 0) {
                    areOnlyZeroes = false;
                    break;
                }
            }
            if (!areOnlyZeroes) ans++;
        }
        return ans;
    }

    Matrix<M, N, Field> transposed() const {
        Matrix<M, N, Field> answer;
        for (size_t i = 0; i < N; ++i) {
            for (size_t j = 0; j < M; ++j) {
                answer[j][i] = matrix[i][j];
            }
        }
        return answer;
    }

    vector<Field> getRow(unsigned i) const {
        vector<Field> row(M);
        for (size_t j = 0; j < N; ++j) {
            row[j] = matrix[i][j];
        }
        return row;
    }

    vector<Field> getColumn(unsigned j) const {
        vector<Field> answer(N);
        for (size_t i = 0; i < N; ++i) {
            answer[i] = matrix[i][j];
        }
        return answer;
    }

    void invert() {
        *this = helpforinvert();
    }

    Matrix inverted() const {
        return helpforinvert();
    }

    Field trace() {
        Field ans = Field(0);
        for (size_t i = 0; i < std::min(N, M); ++i) {
            ans += matrix[i][i];
        }
        return ans;
    }
};

template<size_t N, size_t M, typename Field = Rational>
Matrix<N, M, Field> operator+(const Matrix<N, M, Field>& a, const Matrix<N, M, Field>& b) {
    Matrix<N, M, Field> copy = a;
    copy += b;
    return copy;
}

template<size_t N, size_t M, typename Field = Rational>
Matrix<N, M, Field> operator*(Field a, const Matrix<N, M, Field>& b) {
    Matrix<N, M, Field> copy = b;
    copy *= a;
    return copy;
}

template<size_t N, size_t M, typename Field = Rational>
Matrix<N, M, Field> operator-(const Matrix<N, M, Field>& a, const Matrix<N, M, Field>& b) {
    Matrix<N, M, Field> copy = a;
    copy -= b;
    return copy;
}

template<size_t N, typename Field>
Matrix<N, N, Field> operator-(const Matrix<N, N, Field>& a, const Matrix<N, N, Field>& b) {
    Matrix<N, N, Field> copy = a;
    copy *= b;
    return copy;
}

template<size_t N, typename Field = Rational>
using SquareMatrix = Matrix<N, N, Field>;

template<size_t M, size_t N, size_t K, typename Field>
Matrix<M, K, Field> operator*(const Matrix<M, N, Field>& first, const Matrix<N, K, Field>& second) {
    Matrix<M, K, Field> result;
    for (size_t i = 0; i < M; ++i) {
        for (size_t j = 0; j < K; ++j) {
            result[i][j] = Field(0);
            for (size_t q = 0; q < N; ++q) {
                result[i][j] += first[i][q] * second[q][j];
            }
        }
    }
    return result;
}


