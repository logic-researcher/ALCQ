package preasoner;

import java.util.*;


import formula.Formula;
import roles.AtomicRole;
import convertion.Converter;
import roles.RoleExpression;




public class RoleTreeNode {
    private LinkedList<RoleTreeNode> parentlist;
    private LinkedList<RoleTreeNode> childlist;
    private AtomicRole data;



    public RoleTreeNode(AtomicRole role){
        data = role;
        parentlist = null;
        childlist = null;

    }



    public Set<AtomicRole> getOldersRole(){
        LinkedList<RoleTreeNode> olderList = this.parentlist;
        Set<AtomicRole> OlderRoleList = new HashSet<>();
        if (olderList == null || olderList.isEmpty()){
            return OlderRoleList;
        } else {
            for (RoleTreeNode node : olderList){
                OlderRoleList.add(node.getrole());
                OlderRoleList.addAll(node.getOldersRole());
            }
            return OlderRoleList;
        }

    }


    public Set<AtomicRole> getJuniorsRole(){
        LinkedList<RoleTreeNode> JuniorList = this.childlist;
        Set<AtomicRole> JuniorRoleList = new HashSet<>();
        if (JuniorList == null || JuniorList.isEmpty()){
            return JuniorRoleList;
        } else {
            for (RoleTreeNode node : JuniorList){
                JuniorRoleList.add(node.getrole());
                JuniorRoleList.addAll(node.getJuniorsRole());
            }
            return JuniorRoleList;
        }

    }

    public AtomicRole getrole(){
        return this.data;
    }

    public void addchild(AtomicRole role){
        if(this.childlist==null){
            initChildlist();
            this.childlist.add(Converter.RoleNodeMap.get(role));
        } else {
            this.childlist.add(Converter.RoleNodeMap.get(role));
        }
    }

    public void addparent(AtomicRole role){
        if (this.parentlist==null){
            initParentlist();
            this.parentlist.add(Converter.RoleNodeMap.get(role));
        } else {
            this.parentlist.add(Converter.RoleNodeMap.get(role));
        }
    }

    public void initChildlist(){
        this.childlist = new LinkedList<>();
    }

    public void initParentlist(){
        this.parentlist = new LinkedList<>();
    }

    public LinkedList<RoleTreeNode> getChildlist(){
        return this.childlist;
    }

    public LinkedList<RoleTreeNode> getParentlist(){
        return this.parentlist;
    }





}
