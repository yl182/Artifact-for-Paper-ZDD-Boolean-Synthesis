
#include <sys/types.h>
#include <sys/time.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <stdlib.h>
#include <iostream>
#include <vector>
#include <fstream>   
#include <iterator>
#include <map>
#include <string>  
#include <algorithm>
//reference:https://runestone.academy/runestone/books/published/cppds/Recursion/pythondsConvertinganIntegertoaStringinAnyBase.html
std::string toStr(int n, int base) {
    std::string convertString = "0123456789ABCDEF";
    if (n < base) {
        return std::string(1, convertString[n]); // converts char to string, and returns it
    } else {
        return toStr(n/base, base) + convertString[n%base]; // function makes a recursive call to itself.
    }
}
int main (int argc, char *argv[]){

    const std::string str1(argv[1]);
    int n = std::stoi(str1);

    
    std::cout << "c Yi (for scalable tests only)" << std::endl;

    int CountUni = pow(2, n) + n;
    int CountExi = pow(2,n);
    int CountVar = pow(2,(n+1))+n;
    int CountClause = pow(2,2*n+1);

    std::cout << "c QShifter generator 2021" << std::endl;
    std::cout << "p cnf " << CountVar << " " << CountClause << std::endl;

    std::cout << "a ";
    for (int i = 1; i <= pow(2,n)+n ; i++){
        std::cout << i << " ";
    }
    std::cout << "0" << std::endl;
    
    std::cout << "e ";
    for (int i = pow(2,n)+n+1; i <= 2*pow(2,n)+n ; i++){
        std::cout << i << " ";
        
    }
    std::cout << "0" << std::endl;

    for (int g = 0; g < pow(2,n); g++) {
        // group = 1, ..., 2^n-1
        bool odd =1;
        std::string base2Sign = toStr(g, 2);
        if (base2Sign.length() < n) {
            int diffBits = n-base2Sign.length();
            std::string zerostring = "0";
            for (int t = 0; t < diffBits; t++) {
                base2Sign = zerostring + base2Sign;
            }
            
        }
        char base2Signn[base2Sign.size()+1];
        strcpy(base2Signn, base2Sign.c_str());
        //std::cout << "group " << g << " base2Signn: " << base2Signn << std::endl;
        // std::cout << "bits are: " << (base2Signn[0]=='1') 
        // << (base2Signn[1]=='1') << (base2Signn[2]=='1') 
        // <<(base2Signn[3]=='1') << std::endl;
        //for (char& c : base2Sign) {
            //std::cout<< base2Sign.size() << " " << base2Sign.length();
        // every clause
        for (int cl = 1; cl <=pow(2,n+1); cl++) {
            // 1...n
            for (int k = 1; k <= n; k++) {
                
                // << (base2Sign[0]=='1') << std::endl
                // << (base2Sign[1]=='1') << std::endl
                // << (base2Sign[2]=='1') << std::endl
                // << std::endl;
                if (base2Sign[n-k] == '1') {
                    std::cout << k << " ";
                } else {
                    std::cout << (-1)*k << " ";
                }

            }
            // n+1 th
            
            if (odd == 1){
                std::cout << n+(cl+1)/2 << " ";
                
            }  else {
                std::cout << (-1)*(n+(cl+1)/2) << " ";
                
            }
            //n+2 th
            int val1 = pow(2,n)+n+1;
            int val2 = pow(2,n)*2+n;
            int tempval = (cl-1)/2+val1+g;
            if (tempval > val2) {
                tempval = tempval-pow(2,n);
            }
            if (odd == 0){
                std::cout << tempval << " ";
                odd=1;
            }  else {
                std::cout << (-1)*tempval << " ";
                odd=0;
            }

            
            std::cout << "0" <<std::endl;
        }
        
            // sign: (base2Sign[j]=='1')
            
    }
    
    return 0;
}