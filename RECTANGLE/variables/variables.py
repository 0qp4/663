class Variable:
    def __init__(self, bitsize, value = None, ID = None, copyorigin = None):
        self.bitsize = bitsize
        self.value = value
        self.ID = ID
        self.connected_vars = []
        self.copied_vars = []
        self.copyorigin = copyorigin

    def display_value(self, representation='binary'):
        if representation == 'binary' and self.value:
            return bin(self.value)[2:].zfill(self.bitsize)
        elif representation == 'hexadecimal' and self.value:
            return hex(self.value)[2:].zfill((self.bitsize + 3) // 4)
        elif representation == 'integer':
            return str(self.value)
        else:
            return "Invalid representation"

    def display(self, representation='binary'):
        print("ID: " + self.ID + " / bitsize: " + str(self.bitsize) + " / value: " + self.display_value(representation))

    def remove_round_from_ID(self):
        return '_'.join(part for i, part in enumerate(self.ID.split("_")) if i != 1)
