// g++ -g -Wall -std=c++11 search.cpp
#include <iostream>
#include <vector>
#include <cstring>
#include <algorithm>
#include <array>
#include <unordered_set>
#include <chrono>
#include <iomanip>



using namespace std;

const int BASE = 1000;

struct bignum {
    vector<int> num;

    bignum() { num.resize(1); num[0] = 0; }

    bignum(int x) {
        while (x) {
            num.push_back(x % BASE);
            x /= BASE;
        }
        if (num.empty()) num.push_back(0);
    }

    bignum(const char *s) {
        int len = strlen(s);
        for (int i = len - 1; i >= 0; i -= 3) {
            int tmp = s[i] - '0';
            tmp += (i >= 1) ? (s[i-1] - '0') * 10 : 0;
            tmp += (i >= 2) ? (s[i-2] - '0') * 100 : 0;
            num.push_back(tmp);
        }
        if (num.empty()) num.push_back(0);
    }

    bool operator < (const bignum &a) const {
        if (num.size() != a.num.size()) return num.size() < a.num.size();
        for (int i = num.size() - 1; i >= 0; i--)
            if (num[i] != a.num[i])
                return num[i] < a.num[i];
        return false;
    }

    bool operator == (const bignum &a) const {
        if (num.size() != a.num.size()) return false;
        for (int i = num.size() - 1; i >= 0; i--)
            if (num[i] != a.num[i])
                return false;
        return true;
    }

    bool operator != (const bignum &a) const {
        return !(*this == a);
    }

    bool operator > (const bignum &a) const {
        return !(*this < a) && (*this != a);
    }

    bool operator <= (const bignum &a) const {
        return (*this < a) || (*this == a);
    }

    bool operator >= (const bignum &a) const {
        return (*this > a) || (*this == a);
    }

    bignum operator + (const bignum &a) const {
        bignum res;
        res.num.resize(max(num.size(), a.num.size()) + 1);
        int carry = 0;
        for (int i = 0; i < res.num.size(); i++) {
            int tmp = carry;
            if (i < num.size()) tmp += num[i];
            if (i < a.num.size()) tmp += a.num[i];
            carry = tmp / BASE;
            res.num[i] = tmp % BASE;
        }
        while (res.num.size() > 1 && res.num.back() == 0) res.num.pop_back();
        return res;
    }

    bignum operator - (const bignum &a) const {
        bignum res;
        res.num.resize(max(num.size(), a.num.size()));
        int borrow = 0;
        for (int i = 0; i < res.num.size(); i++) {
            int tmp = 0;
            if (i < num.size()) tmp += num[i];
            if (i < a.num.size()) tmp -= a.num[i];
            tmp -= borrow;
            borrow = 0;
            if (tmp < 0) {
                tmp += BASE;
                borrow = 1;
            }
            res.num[i] = tmp;
        }
        while (res.num.size() > 1 && res.num.back() == 0) res.num.pop_back();
        return res;
    }

    bignum operator * (const bignum &a) const {
        bignum res;
        res.num.resize(num.size() + a.num.size() + 1);
        fill(res.num.begin(), res.num.end(), 0);
        for (int i = 0; i < num.size(); i++) {
            int carry = 0;
            for (int j = 0; j < a.num.size(); j++) {
                int tmp = num[i] * a.num[j] + carry + res.num[i + j];
                carry = tmp / BASE;
                res.num[i + j] = tmp % BASE;
            }
            res.num[i + a.num.size()] += carry;
        }
        while (res.num.size() > 1 && res.num.back() == 0) res.num.pop_back();
        return res;
    }

    bignum pow(int a) const {
        bignum res = 1, base = *this;
        while (a) {
            if (a & 1) res = res * base;
            base = base * base;
            a = a >> 1;
        }
        return res;
    }

    void shrink() {
        while (num.size() > 1 && num.back() == 0) num.pop_back();
        if (num.empty()) num.push_back(0);
    }

};

bignum half(bignum n) {
    bignum res = n;
    int cur = 0;
    for (int i = res.num.size() - 1; i >= 0; i--) {
        int tmp = res.num[i] + cur * BASE;
        res.num[i] = tmp >> 1;
        cur = tmp - (res.num[i] << 1);
    }
    res.shrink();
    return res;
}

bool isPower(bignum n, int k) {
    bignum left = bignum(0), right = n;
    while (left <= right) {
        bignum mid = half(left + right);
        if (mid.pow(k) > n) right = mid - 1;
        else if (mid.pow(k) < n) left = mid + 1;
        else return true;
    }
    return false;
}


string toString(bignum a) {
    string s = "";
    for (int i = a.num.size() - 1; i >= 0; i--) {
        s += to_string(a.num[i]);
    }
    return s;
}

bignum mod(bignum a, bignum b) {
    if (a < b) {
        return a;
    }
    while (a >= b) {
        a =  a - b;
    }

    return a;
}
   
bignum gcd(bignum a, bignum b) {
    while(b != bignum(0)) {
        bignum tmp = mod(a, b);
        a = b;
        b = tmp;
    }
    return a;
}


ostream& operator<<(ostream& os, const bignum& a) {
    os << toString(a);
    return os;
}


bool isPrime(int n) {
    if (n <= 1) {
        return false;
    }
    
    for (int i = 2; i * i <= n; ++i) {
        if (n % i == 0) {
            return false;
        }
    }
    
    return true;
}

bool hasSum(vector<bignum>& nums) {
    auto start = chrono::steady_clock::now(); 
    int n = nums.size();
    unordered_set<string> hashSet; // 将vector中的数存储到哈希表中
    for (auto num : nums){
        hashSet.emplace(toString(num));
    }
    for (int i = 0; i < n - 1; i++) {
        auto end = chrono::steady_clock::now();
        double time = chrono::duration_cast<chrono::microseconds>(end - start).count() / double(1000000); // 转换为秒
        cout << "Now: " << i+1 << " / " << n << " Time: " << fixed << setprecision(0) << time << "s Left:" << (n-i-1) * time / (i+1)  << "s" <<  endl;
        for (int j = i + 1; j < n; j++) {
            if (nums[i] <= nums[j]) continue;
            // 在哈希表中查找是否存在target
            if (hashSet.find(toString(nums[i] + nums[j])) != hashSet.end()) {
                return true; // 存在两个数之和等于第三个数，返回true
            }
            if (hashSet.find(toString(nums[i] - nums[j])) != hashSet.end()) {
                return true; // 存在两个数之和等于第三个数，返回true
            }
        }
    }
    return false;
}

int main() {
    double N = 511;
    int s0 = 20;

    std::vector<bignum> S;
    bignum one = bignum(1), two = bignum(2);
    S.push_back(one);

    bignum M = two.pow(int(N/2./log(2))+1)+one;
    bignum y = two, ys = two.pow(s0);
    while (ys < M) {
        S.push_back(ys);
        // cout << ys << endl;
        ys = ys * y;
        while (ys < M) {
            S.push_back(ys);
            ys = ys * y;
            // cout << ys << endl;
        }
        y = y + 1;
        ys = y.pow(s0);
    }
    int S_size = S.size();
    cout << "S_size = " << S_size << endl;
    std::sort(S.begin(), S.end());

    bool flag = hasSum(S);
    cout << "Have solution? " << (flag? "Yes!":"No!" )<< endl;
    return 0;
}
