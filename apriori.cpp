#include<iostream>
#include<ctime>
#include<math.h>
#include<string>
#include<map>
#include<set>
#include<bits/stdc++.h>
#include<vector>
#include <fstream>

using namespace std;

struct Frequent
{
    int k; //number of members in each itemset
    map<set<int>,int> itemsets; //itemsets contains an itemset of size k along with its corresponding counter
};

vector<Frequent>frequents;
vector<set<int>>transactions;
set<int>ret;
int nowStep=0;
ofstream outfile;
int number_of_strong_rules=0, num=0;
float min_support, min_confidence, total_transactions=0;


//https://stackoverflow.com/questions/11809502/which-is-better-way-to-calculate-ncr

int nCr(int n, int r)
{
    int res = 1;
    int i;

    for(i=1; i<=r; i++)
    {
        res=res*(n-r+i);
        res=res/i;
    }

    return res;
}

Frequent construct(string file_name)
{

    ifstream infile(file_name);
    string line;
    int item;
    Frequent f;
    f.k=1;

    while(getline(infile,line))
    {

        istringstream iss(line);
        total_transactions+=1;
        set<int>transaction;

        while( iss >> item )
        {

            set<int> item_set;
            item_set.insert(item);

            ret.insert(item);

            transaction.insert(item);

            if(f.itemsets.count(item_set)>0)
            {
                f.itemsets[item_set]+=1;
            }
            else
            {
                f.itemsets.insert(pair<set<int>,int>(item_set,1));
            }
        }

        transactions.push_back(transaction);
    }

    infile.close();

    return f;

}

//https://stackoverflow.com/questions/29200635/convert-float-to-string-with-precision-number-of-decimal-digits-specified
string to_string_round(float n)
{
    stringstream stream;
    stream << fixed << setprecision(3) << n;
    string s = stream.str();
    return s;
}


void print_association_rules(set<int> &trans, set<int> &head, int count_f, float conf)
{

    vector<int> tail(trans.size());

    //https://www.geeksforgeeks.org/std-set_difference-in-cpp/
    vector<int>::iterator it=set_difference(trans.begin(),trans.end(),head.begin(),head.end(),tail.begin());

    string text ="";

    for (auto itr = head.begin(); itr != head.end(); )
    {
        text += to_string(*itr);
        if(++itr ==head.end())
        {
            text += " -> ";
        }
        else
        {
            text += ", ";
        }
    }


    for (auto itr = tail.begin(); itr < it; ++itr)
    {
        text += to_string(*itr);
        if(itr+1==it)
        {
            text += " ";
        }
        else
        {
            text += ", ";
        }
    }

    string confidence = to_string_round(conf);
    string support = to_string_round(count_f/total_transactions);

    text += "(" + support + "," + confidence + ")";

    outfile<<text;
    outfile<<endl;

}


// Finds all the subsets of one transaction and increments their counters in candidate itemsets if found (when count_f=-1)
// Generates all combination of rules possible with the members of each itemset and prints the ones that are strong (when count_f!=-1)
// https://stackoverflow.com/questions/4555565/generate-all-subsets-of-size-k-from-a-set
void subset(set<int> &trans, int len, int left, set<int>::iterator index, set<int> &l, Frequent &f, int count_f)
{

    if(left==0)
    {

        if(count_f==-1)
        {

            if(f.itemsets.count(l)>0)
            {
                f.itemsets[l]+=1;
            }

        }
        else
        {

            float count_s=frequents[l.size()-1].itemsets[l];
            float conf = (float)count_f/count_s;

            if(conf >= min_confidence)
            {
                number_of_strong_rules +=1;
                if(num==0)
                {
                    print_association_rules(trans, l, count_f, conf);
                }
            }

        }

        return;

    }

    for(set<int>::iterator it=index; it!=trans.end(); ++it)
    {
        l.insert(*it);
        subset(trans,len,left-1,++index,l,f, count_f);
        l.erase(*it);
    }
    return;
}


void generate_one_item_frequent_set(Frequent f)
{

    Frequent f1;
    f1.k=1;

// push the frequent one items into frequents
    for(auto itr = f.itemsets.begin(); itr!=f.itemsets.end(); ++itr)
    {
        if (itr->second >= min_support)
        {
            f1.itemsets.insert(pair<set<int>,int>(itr->first,itr->second));
        }
    }

    frequents.push_back(f1);
    //cout<<frequents.size()<<endl;

    return;

}

//check to see if all subsets of the newly created set are frequent i.e present in the previous list
bool check_candidate_subsets(set<int>temp1, Frequent old_set)
{

    set<int>temp;
    temp=temp1;
    bool flag=true;

    for (auto it=temp1.begin(); it!= temp1.end(); ++it)
    {
        temp.erase(*it);
        if(old_set.itemsets.count(temp)==0)
        {
            flag= false;
            temp.insert(*it);
            break;
        }
        temp.insert(*it);
    }

    return flag;

}


void generate_candidate_sets(Frequent &new_set, Frequent &old_set)
{

    Frequent temp_set;
    bool flag;
    set<int> unique_items, temp, temp1;
    new_set.k = old_set.k + 1;

// create a set with all the distinct items
    for(auto itr=old_set.itemsets.begin(); itr!=old_set.itemsets.end(); ++itr)
    {
        temp=itr->first;
        unique_items.insert(temp.begin(),temp.end());
    }

// create k+1 itemsets through every possible combination
    for(auto itr1=old_set.itemsets.begin(); itr1!=old_set.itemsets.end(); ++itr1)
    {

        temp1=itr1->first;

        for(auto itr2=unique_items.begin(); itr2!=unique_items.end(); ++itr2)
        {

            if(temp1.count(*itr2)==0)
            {
                temp1.insert(*itr2);

                if(new_set.itemsets.count(temp1)==0)
                {
                    temp_set.itemsets.insert(pair<set<int>,int>(temp1,0));
                }

                temp1.erase(*itr2);
            }

        }

    }

// for every k+1 itemset created, only keep the ones whose subsets are frequent (i.e subsets are present in the previous k itemsets)
    for(auto itr1=temp_set.itemsets.begin(); itr1!=temp_set.itemsets.end(); ++itr1)
    {

        temp1=itr1->first;
        temp=temp1;
        flag=true;

        for (auto itr2=temp1.begin(); itr2!= temp1.end(); ++itr2)
        {
            temp.erase(*itr2);

            if(old_set.itemsets.count(temp)==0)
            {
                flag=false;
                break;
            }

            temp.insert(*itr2);
        }

        if(flag)
        {
            new_set.itemsets.insert(pair<set<int>,int>(temp1,0));
        }

    }

    return;

}

// Only keeps the frequent itemsets in the set
// Goes to each transaction and finds subsets of size k and increments their count. This is done in the function subset()
// If the number of candidates in itemsets is less than the number of subsets of size k of one transaction, it loops over each candidate itemsets instead
// and checks whether it is in the transaction or not (increments the count if it is)

void prune(Frequent &f)
{

    int temp_count, n;
    bool inc;

    set<int>temp_set, transaction, help_set;


    for (int i=0; i<transactions.size(); i++)
    {

        transaction=transactions[i];

        if(f.k<=transaction.size())
        {

            n = nCr(transaction.size(), f.k);

            if(f.itemsets.size()>=n)
            {

                //the subset function is used for generating transaction subsets when count_f is set to -1 and rules otherwise
                subset(transaction,transaction.size(),f.k,transaction.begin(),help_set,f,-1);
            }

            else
            {

                for(auto itr1=f.itemsets.begin(); itr1!=f.itemsets.end(); ++itr1)
                {
                    temp_set=itr1->first;
                    inc=true;

                    for(auto itr2=temp_set.begin(); itr2!=temp_set.end(); ++itr2)
                    {
                        if(transaction.count(*itr2)==0)
                        {
                            inc=false;
                            break;
                        }
                    }

                    if(inc)
                    {
                        f.itemsets[temp_set]+=1;
                    }
                }

            }
        }
    }


    Frequent f_new;
    f_new.k = f.k;

    for (auto it = f.itemsets.begin(); it!=f.itemsets.end(); ++it)
    {
        if (it->second >= min_support)
        {
            f_new.itemsets.insert(pair<set<int>,int>(it->first, it->second));
        }
    }
    f.itemsets.clear();
    frequents.push_back(f_new);

    return;

}

void print_frequent_itemsets()
{

    Frequent f;
    set<int> temp;
    string m, line;
    float n;

    outfile.open("frequent_itemsets.txt");

    for(int i=0; i<frequents.size(); i++)
    {

        f = frequents[i];
        for (auto itr1 = f.itemsets.begin(); itr1 != f.itemsets.end(); ++itr1)
        {
            temp = itr1->first;
            n = (float) itr1->second;
            //cout<<n/total_transactions<<endl;
            m = to_string_round(n/total_transactions);

            auto itr2=temp.begin();

            while(itr2!=temp.end())
            {
                outfile<<*itr2;

                if(++itr2!=temp.end())
                {
                    outfile<<", ";
                }
                else
                {
                    outfile<<" ";
                }
            }

            line="(" + m + ")";
            outfile<<line;
            outfile<<endl;
        }

    }
    outfile.close();
    return;
}

// Uses the subset function to generate rules with the members of each itemset and prints the rules that are strong
void generate_association_rules()
{

    set<int> l, itemset;
    if(num==0)
    {
        outfile.open("strong_rules.txt");
    }
    int count_f;
    Frequent f;

    for(int i=1; i<frequents.size(); i++)
    {
        f=frequents[i];
        for (auto it = f.itemsets.begin(); it != f.itemsets.end(); ++it)
        {
            itemset=it->first;
            count_f=it->second;
            for(int j=1; j<itemset.size(); j++)
            {
                subset(itemset,itemset.size(),j,itemset.begin(), l, f, count_f);
            }
        }
    }

    if(num==0)
    {
        outfile.close();
    }

    if(num==1)
    {
        cout<<"Number of association rules: "<<number_of_strong_rules<<endl;
    }

}

void print_frequent_numbers()
{

    Frequent f;
    string line;

    for(int i=1; i<=frequents.size(); i++)
    {
        f=frequents[i-1];
        line="Number of frequent " + to_string(i) + "_itemsets: " + to_string(f.itemsets.size());
        cout<<line<<endl;
    }

}


int main(int argc, char **argv)
{

    if(argc<4 || argc>5)
	{
		//cout<< "Incorrect number of arguments, terminating the program...";
		return 0;
	}

    string fileName = string(argv[1]);
    //cout<<fileName<<endl;
	min_confidence = atof(argv[3]);
	//cout<<min_confidence<<endl;
    char show;

	if(argc==4){
        show = 'o';
	}
	else if(argc==5){
        show = *(argv[4]);
	}

	//cout<<show<<endl;

   /* string fileName="data10k.txt";
    float min_support_ratio=0.001;
    min_confidence=0.8;
    char show='a'; */

// Starts the clock to calculate the execution time
    const clock_t begin_time=clock();

// Reads each line of transactions from the file, counts the total number of transactions and creates a candidate set of one items (k=1)
    Frequent f = construct(fileName);

    min_support = round(atof(argv[2]) * total_transactions);
    //cout<<min_support<<endl;
    //min_support = min_support_ratio * total_transactions;

// Creates a set of one items that are frequent
    generate_one_item_frequent_set(f);

    Frequent f1;
    Frequent f2 = frequents[0];

// Generates k+1 frequent item sets from previous frequent k item sets
    while(f2.itemsets.size()!=0)
    {

        // Generates k+1 item sets (f1) from previous frequent k item sets (f2)
        generate_candidate_sets(f1,f2);

        // Removes the non-frequent k+1 itemsets from f1 and pushes the k+1 frequent item sets into frequents
        prune(f1);

        // Newly pushed k+1 frequent itemsets becomes f2
        f2=frequents.back();
    }

    frequents.pop_back();

    switch(show)
    {

    case 'r':
        generate_association_rules();
        cout<<"File(s) generated!"<<endl;
        break;
    case 'f':
        num=1;
        print_frequent_itemsets();
        cout<<"File(s) generated!"<<endl;
        break;
    case 'a':
        print_frequent_itemsets();
        generate_association_rules();
        cout<<"File(s) generated!"<<endl;
        break;
    case 'o':
        num=1;
        //cout<<"hi"<<endl;
        print_frequent_numbers();
        generate_association_rules();
        break;
    }


    float seconds = float ( float( clock() - begin_time )/CLOCKS_PER_SEC );

    cout<<"Total Execution Time: "<<seconds<<" seconds"<<endl;


    return 0;
}


