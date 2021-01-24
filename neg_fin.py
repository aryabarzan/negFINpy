import csv
from datetime import datetime
from math import ceil
from bitarray import bitarray


class BMCTreeNode:
    """
    The node in the BMC tree.

    Note: To get more information about the fields, refer to the supporting paper.

    Attributes:
        item (int): The item (really the index of item) which is registered in this node.
        count (int): The number of transactions reached to this node.
        bitmap_code (bitarray): The bitmap representation of itemset registered from root to this node.
            children (dict): The list of children of this node.
            This dictionary maps each child item to child node for speeding up
            accessing to the child node by its item.
            child.item ==> child
    """

    def __init__(self, item, count, bitmap_code):
        self.item = item
        self.count = count
        self.bitmap_code = bitmap_code
        self.children = dict()

    def get_child_registering_item(self, item):
        """
        Return the child which registers the specified item.
        If does not exist such child, then return None.

        Args:
            item (int): The item (really the index of item).

        Returns:
            The BMCTreeNode that is child of this node and registers item.
        """
        return self.children.get(item)

    def add_child(self, child):
        self.children[child.item] = child

    def __repr__(self):
        return f'{self.item}:{self.count}->{self.bitmap_code}'


class FrequentItemsetTreeNode:
    def __init__(self):
        self.item = None
        self.count = 0
        self.children = []
        self.NegNodeSet = []

    def __repr__(self):
        return f'{self.item}'


def clean_BMC_tree(root):
    """
    Delete two fields item and children from the root and all of its descendants.

    Args:
        root (BMCTreeNode): The root of sub-tree
    """
    for item, child in root.children.items():
        clean_BMC_tree(child)
    del root.item
    del root.children


class NegFIN:
    def __init__(self, dataset_file, min_support, output_file, delimiter=' '):
        self.dataset_file = dataset_file
        self.min_support = min_support  # The relative minimum support
        self.min_count = None  # The absolute minimum support
        self.output_file = output_file
        self.delimiter = delimiter
        self.num_of_transactions = None
        self.F1 = None
        self.item_to_NodeSet = None
        self.writer = None
        self.num_of_frequent_itemsets = 0;
        self.execution_time = None

    def __find_F1(self):
        """
        Scanning DB to find F1, the set of frequent items.
        """
        item_name_to_count = {}  # Holds the count of each item
        with open(self.dataset_file) as file_input:
            reader = csv.reader(file_input, delimiter=self.delimiter)
            self.num_of_transactions = 0
            for transaction in reader:
                self.num_of_transactions += 1
                for item_name in transaction:
                    item_count = item_name_to_count.setdefault(item_name, 0)
                    item_name_to_count[item_name] = item_count + 1

        item_name_to_count.pop('', None)  # Removing the empty item_name if exists.
        self.min_count = ceil(self.num_of_transactions * self.min_support)
        # Removing infrequent items and making F1
        self.F1 = [{'name': item_name, 'count': item_count} for (item_name, item_count) in item_name_to_count.items() if
                   self.min_count <= item_count]
        # Sorting F1 in ascending order of items' count
        self.F1.sort(key=lambda item: item['count'])
        self.F1 = tuple(self.F1)  # Converting to a tuple to speed up

    def __generate_NodeSets_of_1_itemsets(self):
        """
        Generate the BMCtree.
        During generation, insert each node to the appropriate NodeSet.
        """

        # Assigning a unique index to each item.
        # From this point forward, we use the item index to refer the item
        item_name_to_item_index = {item['name']: item_index for (item_index, item) in enumerate(self.F1)}
        # Holds the NegNodeSet of each item
        self.item_to_NodeSet = {item_index: [] for item_index in item_name_to_item_index.values()}
        # Creating and initializing the root of BMCTree
        bmc_tree_root = BMCTreeNode(item=None, count=None, bitmap_code=bitarray([False] * len(self.F1)))

        with open(self.dataset_file) as fInput:
            reader = csv.reader(fInput, delimiter=self.delimiter)
            for transaction in reader:
                # Removing infrequent items from transaction,
                # and converting frequent items in it to the corresponding indices
                transaction = [item_name_to_item_index[item_name] for item_name in transaction if
                               item_name in item_name_to_item_index]
                # Sorting the transaction in descending order of items' index
                # Please note that items' index have a direct relation with items' count
                transaction.sort(reverse=True)

                # Inserting transaction to the BMCTree
                cur_root = bmc_tree_root
                for item in transaction:
                    N = cur_root.get_child_registering_item(item)
                    if N is None:
                        bitmap_code = cur_root.bitmap_code.copy()
                        bitmap_code[item] = True
                        N = BMCTreeNode(item=item, count=0, bitmap_code=bitmap_code)
                        cur_root.add_child(N)
                        self.item_to_NodeSet[item].append(N)

                    N.count += 1
                    cur_root = N

        # After creation of the NodeSets of 1-itemset, some fields of BMCTreeNode will be unusable.
        # So, to save the memory space, two fields item and children are deleted.
        clean_BMC_tree(bmc_tree_root)

    def __create_root_of_frequent_itemset_tree(self):
        """"
         Create the root of frequent itemset tree and
         level 1 of frequent itemset tree and.
         This tree is not explicitly built.
         It represents the search space which is traversed in depth-first order.
        """
        root = FrequentItemsetTreeNode()

        for item in range(len(self.F1)):
            child = FrequentItemsetTreeNode()
            child.item = item
            child.count = self.F1[item]['count']
            child.NegNodeSet = self.item_to_NodeSet[item]
            root.children.append(child)
        return root

    def __write_itemsets_to_file(self, N, itemset_buffer, N_itemset_length, FIS_parent_buffer, FIS_parent_length):
        """
        Write the itemset represented by 'N',
         and all combination that can be made using this itemset and all subsets of FIS_parent,
         to the output file.
        Args:
            Similar to '__construct_frequent_itemset_tree'
        Returns:
            Write the discovered frequent itemset into the output file.
        """
        # Create a buffer for writing to file
        file_buffer = []

        self.num_of_frequent_itemsets += 1
        # Get the real name (string name) of items
        itemset_string = [self.F1[itemset_buffer[i]]['name'] for i in range(N_itemset_length)]
        # Append the count of the itemset
        itemset_string.append('#SUP: {0}\n'.format(N.count))
        line = ' '.join(itemset_string)
        file_buffer.append(line)

        # === Write all combination that can be made using this itemset and all subsets of FIS_parent
        if FIS_parent_length > 0:
            # Generate all subsets of the node list except the empty set
            max = 1 << FIS_parent_length
            for i in range(1, max):
                # Get the real name of items
                itemset_string = [self.F1[itemset_buffer[i]]['name'] for i in range(N_itemset_length)]
                # We create a new subset
                # Check if the j bit is set to 1. #isSet = i & (1 << j)
                subsetString = [self.F1[FIS_parent_buffer[j]]['name'] for j in range(FIS_parent_length) if
                                (i & (1 << j)) > 0]
                # Concatenate the itemset with the subset
                itemset_string.extend(subsetString)
                # Append the count of the itemset
                itemset_string.append('#SUP: {0}\n'.format(N.count))
                line = ' '.join(itemset_string)
                file_buffer.append(line)

                self.num_of_frequent_itemsets += 1

        # Write the file_buffer to file and create a new line
        # so that we are ready for writing the next itemset.
        self.writer.writelines(file_buffer)

    def __construct_frequent_itemset_tree(self, N, itemset_buffer, N_itemset_length, N_right_siblings,
                                          FIS_parent_buffer,
                                          FIS_parent_length):
        """
         This is a recursive method which is traverse the search space in depth-first order.
         It implicitly builds the itemset tree.
        Args:
            N (:obj:'FrequentItemsetTreeNode'): The current visited node in the implicit itemset tree.
            itemset_buffer (:obj:`list` of int): The buffer for storing the itemset represented by node 'N'.
                Each member of it represents an item index.
            N_itemset_length (int): Cardinality of the itemset represented by N.
                The itemset represented by N is denoted by  'N_itemset_length[0:N_itemset_length]'
            N_right_siblings (:obj:`list` of :obj:'FrequentItemsetTreeNode'):
                The sibling nodes of 'N'
            FIS_parent_buffer (:obj:`list` of int):
                The buffer for storing FIS, a set of equivalent items of the parent of 'N'.
                For more information, refer to the supporting paper.
            FIS_parent_length (): # Cardinality of FIS.

        Returns:
            Write the discovered frequent itemset into the output file.
        """
        for sibling in N_right_siblings:
            child = FrequentItemsetTreeNode()
            sum_of_NegNodeSets_counts = 0
            if N_itemset_length == 1:  # means at level 1
                for ni in N.NegNodeSet:
                    if not ni.bitmap_code[sibling.item]:
                        child.NegNodeSet.append(ni)
                        sum_of_NegNodeSets_counts += ni.count
            else:
                for nj in sibling.NegNodeSet:
                    if nj.bitmap_code[N.item]:
                        child.NegNodeSet.append(nj)
                        sum_of_NegNodeSets_counts += nj.count

            child.count = N.count - sum_of_NegNodeSets_counts
            if self.min_count <= child.count:
                if N.count == child.count:
                    FIS_parent_buffer[FIS_parent_length] = sibling.item
                    FIS_parent_length += 1
                else:
                    child.item = sibling.item
                    N.children.append(child)

        # Write itemset(s) to file
        self.__write_itemsets_to_file(N, itemset_buffer, N_itemset_length, FIS_parent_buffer, FIS_parent_length)

        number_of_childeren = len(N.children)
        for childIndex in range(number_of_childeren):
            child = N.children[0]
            itemset_buffer[N_itemset_length] = child.item
            del N.children[0] # We delete this node since it is not used anymore.
            self.__construct_frequent_itemset_tree(child, itemset_buffer, N_itemset_length + 1, N.children,
                                                   FIS_parent_buffer, FIS_parent_length)

    def runAlgorithm(self):
        start_timestamp = datetime.now()
        self.__find_F1()
        self.__generate_NodeSets_of_1_itemsets()
        root = self.__create_root_of_frequent_itemset_tree()
        self.writer = open(self.output_file, 'w')
        # The following buffer is used for storing frequent itemsets discovered in a depth.
        itemset_buffer = [None] * len(self.F1)
        # Cardinality of itemset.
        #The current itemset is represented by 'itemset_buffer[0:itemset_length]'.
        itemset_length = 0  # Set the itemset of root to empty

        # The following buffer is used for storing FIS, a set of equivalent items of the parent.
        # For more information, refer to the supporting paper.
        FIS_parent_buffer = [None] * len(self.F1)
        FIS_parent_length = 0
        num_of_children = len(root.children)
        for childIndex in range(num_of_children):
            child = root.children[0]
            itemset_buffer[itemset_length] = child.item
            del root.children[0] # We delete this node since it is not used anymore.
            # Call this recursive method to traverse the search space in a depth-first order.
            self.__construct_frequent_itemset_tree(child, itemset_buffer, itemset_length + 1, root.children,
                                                   FIS_parent_buffer, FIS_parent_length)

        self.writer.close()

        end_timestamp = datetime.now()
        time_diff = (end_timestamp - start_timestamp) # Total execution time of algorithm.
        self.execution_time = time_diff.total_seconds() * 1000

    # Print statistics about the latest execution of the algorithm to
    # standard output
    def printStats(self):
        print('=' * 5 + 'negFIN - STATS' + '=' * 5)
        print(f' Minsup = {self.min_support}\n Number of transactions: {self.num_of_transactions}');
        print(f' Number of frequent  itemsets: {self.num_of_frequent_itemsets}');
        print(f' Total time ~: {self.execution_time} ms');
        #     System.out.println(' Max memory:'
        #             + MemoryLogger.getInstance().getMaxMemory() + ' MB');
        print('=' * 14);


if __name__ == '__main__':
    datasetFile1 = 'H:\\datasets\\chess.dat'  # 'test.dat'; #The database
    outputFile1 = 'outputNegFIN.txt'  # The path for saving the frequent itemsets found.
    delimiter1 = ' '
    minSupport1 = 0.50;  # Means the minimum support. We uses a relative count.

    # Applying the algorithm
    algorithm = NegFIN(datasetFile1, minSupport1, outputFile1, delimiter1)
    algorithm.runAlgorithm()
    algorithm.printStats()
